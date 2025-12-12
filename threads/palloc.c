#include "threads/palloc.h"
#include <bitmap.h>
#include <debug.h>
#include <inttypes.h>
#include <round.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include "threads/loader.h"
#include "threads/synch.h"
#include "threads/vaddr.h"

/* Page allocator.  Hands out memory in page-size (or
   page-multiple) chunks.  See malloc.h for an allocator that
   hands out smaller chunks.

   System memory is divided into two "pools" called the kernel
   and user pools.  The user pool is for user (virtual) memory
   pages, the kernel pool for everything else.  The idea here is
   that the kernel needs to have memory for its own operations
   even if user processes are swapping like mad.

   By default, half of system RAM is given to the kernel pool and
   half to the user pool.  That should be huge overkill for the
   kernel pool, but that's just fine for demonstration purposes. */

/* A memory pool. */
struct pool {
    struct lock lock;        /* Mutual exclusion. */
    struct bitmap *used_map; /* Bitmap of free pages. */
    uint8_t *base;           /* Base of pool. */
    size_t next_fit_pos;     /* Next fit starting position. */
};

/* Two pools: one for kernel data, one for user pages. */
static struct pool kernel_pool, user_pool;

static void init_pool(struct pool *, void *base, size_t page_cnt,
                      const char *name);
static bool page_from_pool(const struct pool *, void *page);

/* Current allocation mode. */
static enum palloc_mode palloc_mode = PAL_FIRST_FIT;

/* Sets the allocation mode. */
void
palloc_set_mode (enum palloc_mode mode)
{
  palloc_mode = mode;
  kernel_pool.next_fit_pos = 0;
  user_pool.next_fit_pos = 0;
}

/* Helper: Round up to next power of 2 */
static size_t
round_up_pow2 (size_t n)
{
  size_t result = 1;
  while (result < n)
    result <<= 1;
  return result;
}

/* Helper: Calculate log2 of n (ceiling) */
static size_t
log2_ceil (size_t n)
{
  size_t order = 0;
  size_t val = 1;
  while (val < n)
    {
      val <<= 1;
      order++;
    }
  return order;
}

/* Next Fit: scan from last position, wrap around if needed */
static size_t
next_fit_scan (struct bitmap *map, size_t *pos, size_t cnt)
{
  size_t idx;
  size_t size = bitmap_size (map);
  
  /* Try from current position to end */
  idx = bitmap_scan (map, *pos, cnt, false);
  
  /* Wrap around if not found */
  if (idx == BITMAP_ERROR && *pos > 0)
    idx = bitmap_scan (map, 0, cnt, false);
  
  /* Update position for next allocation */
  if (idx != BITMAP_ERROR)
    {
      bitmap_set_multiple (map, idx, cnt, true);
      *pos = (idx + cnt) % size;
    }
  
  return idx;
}

/* Best Fit: find smallest hole that fits */
static size_t
best_fit_scan (struct bitmap *map, size_t cnt)
{
  size_t best_idx = BITMAP_ERROR;
  size_t best_size = BITMAP_ERROR;
  size_t i = 0;
  size_t size = bitmap_size (map);
  
  while (i < size)
    {
      if (!bitmap_test (map, i))
        {
          size_t start = i;
          size_t len = 0;
          
          /* Count consecutive free pages */
          while (i < size && !bitmap_test (map, i))
            {
              len++;
              i++;
            }
          
          /* Update best if this hole fits and is smaller */
          if (len >= cnt && len < best_size)
            {
              best_idx = start;
              best_size = len;
              
              /* Exact match - can't do better */
              if (len == cnt)
                break;
            }
        }
      else
        i++;
    }
  
  if (best_idx != BITMAP_ERROR)
    bitmap_set_multiple (map, best_idx, cnt, true);
  
  return best_idx;
}

/* Buddy System: find aligned 2^k block */
static size_t
buddy_scan (struct bitmap *map, size_t cnt)
{
  size_t block_size = round_up_pow2 (cnt);
  size_t size = bitmap_size (map);
  size_t i;
  
  /* Scan for aligned block of size 2^k */
  for (i = 0; i + block_size <= size; i += block_size)
    {
      /* Check if entire block is free */
      if (bitmap_scan (map, i, block_size, false) == i)
        {
          bitmap_set_multiple (map, i, block_size, true);
          return i;
        }
    }
  
  return BITMAP_ERROR;
}

/* Initializes the page allocator.  At most USER_PAGE_LIMIT
   pages are put into the user pool. */
void palloc_init(size_t user_page_limit)
{
    /* Free memory starts at 1 MB and runs to the end of RAM. */
    uint8_t *free_start = ptov(1024 * 1024);
    uint8_t *free_end = ptov(init_ram_pages * PGSIZE);
    size_t free_pages = (free_end - free_start) / PGSIZE;
    size_t user_pages = free_pages / 2;
    size_t kernel_pages;
    if (user_pages > user_page_limit)
        user_pages = user_page_limit;
    kernel_pages = free_pages - user_pages;

    /* Give half of memory to kernel, half to user. */
    init_pool(&kernel_pool, free_start, kernel_pages, "kernel pool");
    init_pool(&user_pool, free_start + kernel_pages * PGSIZE,
              user_pages, "user pool");
}

/* Obtains and returns a group of PAGE_CNT contiguous free pages.
   If PAL_USER is set, the pages are obtained from the user pool,
   otherwise from the kernel pool.  If PAL_ZERO is set in FLAGS,
   then the pages are filled with zeros.  If too few pages are
   available, returns a null pointer, unless PAL_ASSERT is set in
   FLAGS, in which case the kernel panics. */
void *
palloc_get_multiple(enum palloc_flags flags, size_t page_cnt)
{
    struct pool *pool = flags & PAL_USER ? &user_pool : &kernel_pool;
    void *pages;
    size_t page_idx;
    size_t alloc_cnt = page_cnt;

    if (page_cnt == 0)
        return NULL;

    /* For buddy system, round up to power of 2 */
    if (palloc_mode == PAL_BUDDY)
        alloc_cnt = round_up_pow2 (page_cnt);

    lock_acquire(&pool->lock);
    
    /* Select allocation algorithm */
    switch (palloc_mode)
      {
      case PAL_FIRST_FIT:
        page_idx = bitmap_scan_and_flip (pool->used_map, 0, alloc_cnt, false);
        break;
        
      case PAL_NEXT_FIT:
        page_idx = next_fit_scan (pool->used_map, &pool->next_fit_pos, alloc_cnt);
        break;
        
      case PAL_BEST_FIT:
        page_idx = best_fit_scan (pool->used_map, alloc_cnt);
        break;
        
      case PAL_BUDDY:
        page_idx = buddy_scan (pool->used_map, alloc_cnt);
        break;
        
      default:
        page_idx = BITMAP_ERROR;
        break;
      }
    
    lock_release(&pool->lock);

    if (page_idx != BITMAP_ERROR)
        pages = pool->base + PGSIZE * page_idx;
    else
        pages = NULL;

    if (pages != NULL) {
        if (flags & PAL_ZERO)
            memset(pages, 0, PGSIZE * alloc_cnt);
    } else {
        if (flags & PAL_ASSERT)
            PANIC("palloc_get: out of pages");
    }

    return pages;
}

/* Obtains a single free page and returns its kernel virtual
   address.
   If PAL_USER is set, the page is obtained from the user pool,
   otherwise from the kernel pool.  If PAL_ZERO is set in FLAGS,
   then the page is filled with zeros.  If no pages are
   available, returns a null pointer, unless PAL_ASSERT is set in
   FLAGS, in which case the kernel panics. */
void *
palloc_get_page(enum palloc_flags flags)
{
    return palloc_get_multiple(flags, 1);
}

/* Frees the PAGE_CNT pages starting at PAGES. */
void palloc_free_multiple(void *pages, size_t page_cnt)
{
    struct pool *pool;
    size_t page_idx;
    size_t free_cnt = page_cnt;

    ASSERT(pg_ofs(pages) == 0);
    if (pages == NULL || page_cnt == 0)
        return;

    if (page_from_pool(&kernel_pool, pages))
        pool = &kernel_pool;
    else if (page_from_pool(&user_pool, pages))
        pool = &user_pool;
    else
        NOT_REACHED();

    page_idx = pg_no(pages) - pg_no(pool->base);

    /* For buddy system, free the rounded-up amount */
    if (palloc_mode == PAL_BUDDY)
        free_cnt = round_up_pow2 (page_cnt);

#ifndef NDEBUG
    memset(pages, 0xcc, PGSIZE * free_cnt);
#endif

    ASSERT(bitmap_all(pool->used_map, page_idx, free_cnt));
    bitmap_set_multiple(pool->used_map, page_idx, free_cnt, false);
}

/* Frees the page at PAGE. */
void palloc_free_page(void *page)
{
    palloc_free_multiple(page, 1);
}

/* Returns the index of the page in the pool's bitmap. */
size_t
palloc_get_page_index (void *page)
{
  struct pool *pool;

  if (page_from_pool (&kernel_pool, page))
    pool = &kernel_pool;
  else if (page_from_pool (&user_pool, page))
    pool = &user_pool;
  else
    return BITMAP_ERROR;

  return pg_no (page) - pg_no (pool->base);
}

/* Initializes pool P as starting at START and ending at END,
   naming it NAME for debugging purposes. */
static void
init_pool(struct pool *p, void *base, size_t page_cnt, const char *name)
{
    /* We'll put the pool's used_map at its base.
     Calculate the space needed for the bitmap
     and subtract it from the pool's size. */
    size_t bm_pages = DIV_ROUND_UP(bitmap_buf_size(page_cnt), PGSIZE);
    if (bm_pages > page_cnt)
        PANIC("Not enough memory in %s for bitmap.", name);
    page_cnt -= bm_pages;

    printf("%zu pages available in %s.\n", page_cnt, name);

    /* Initialize the pool. */
    lock_init(&p->lock);
    p->used_map = bitmap_create_in_buf(page_cnt, base, bm_pages * PGSIZE);
    p->base = base + bm_pages * PGSIZE;
    p->next_fit_pos = 0;
}

/* Returns true if PAGE was allocated from POOL,
   false otherwise. */
static bool
page_from_pool(const struct pool *pool, void *page)
{
    size_t page_no = pg_no(page);
    size_t start_page = pg_no(pool->base);
    size_t end_page = start_page + bitmap_size(pool->used_map);

    return page_no >= start_page && page_no < end_page;
}
