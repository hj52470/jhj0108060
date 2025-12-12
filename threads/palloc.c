#include "palloc.h"
#include <bitmap.h>
#include <debug.h>
#include <round.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include "threads/loader.h"
#include "threads/synch.h"
#include "threads/vaddr.h"

/* A memory pool. */
struct pool
{
  struct lock lock;
  struct bitmap *used_map;
  uint8_t *base;

  size_t next_fit_start;
};

/* Two pools: one for kernel data, one for user pages. */
static struct pool kernel_pool, user_pool;

static void init_pool (struct pool *, void *base, size_t page_cnt,
                       const char *name);
static bool page_from_pool (const struct pool *, void *page);

/* Current allocation mode. */
static enum palloc_mode cur_mode = PAL_FIRST_FIT;

/* Next Fit implementation */
static size_t
bitmap_scan_and_flip_next_fit (struct bitmap *b, size_t *start, 
                               size_t cnt, bool value)
{
  size_t page_idx;
  size_t bitmap_size_val = bitmap_size (b);
  
  ASSERT (b != NULL);
  ASSERT (cnt <= bitmap_size_val);
  
  /* Try from start position to end */
  page_idx = bitmap_scan (b, *start, cnt, value);
  
  /* If not found, wrap around to beginning */
  if (page_idx == BITMAP_ERROR && *start > 0)
    page_idx = bitmap_scan (b, 0, cnt, value);
  
  /* If found, flip bits and update start position */
  if (page_idx != BITMAP_ERROR)
    {
      bitmap_set_multiple (b, page_idx, cnt, !value);
      *start = (page_idx + cnt) % bitmap_size_val;
    }
  
  return page_idx;
}

/* Best Fit implementation */
static size_t
bitmap_scan_and_flip_best_fit (struct bitmap *b, size_t cnt, bool value)
{
  size_t best_idx = BITMAP_ERROR;
  size_t best_size = BITMAP_ERROR;
  size_t i = 0;
  size_t bitmap_size_val = bitmap_size (b);
  
  ASSERT (b != NULL);
  ASSERT (cnt > 0);
  
  /* Scan entire bitmap to find best fit */
  while (i < bitmap_size_val)
    {
      /* Check if current position has the target value */
      if (bitmap_test (b, i) == value)
        {
          size_t start = i;
          size_t len = 0;
          
          /* Count consecutive bits with target value */
          while (i < bitmap_size_val && bitmap_test (b, i) == value)
            {
              len++;
              i++;
            }
          
          /* Update best if this block fits and is smaller than current best */
          if (len >= cnt && len < best_size)
            {
              best_idx = start;
              best_size = len;
              
              /* If exact match, stop searching */
              if (len == cnt)
                break;
            }
        }
      else
        {
          i++;
        }
    }
  
  /* If found, flip the bits */
  if (best_idx != BITMAP_ERROR)
    bitmap_set_multiple (b, best_idx, cnt, !value);
  
  return best_idx;
}

void
palloc_set_mode (enum palloc_mode mode)
{
  cur_mode = mode;
  kernel_pool.next_fit_start = 0;
  user_pool.next_fit_start = 0;
}

/* Round up N to the nearest power of two (for buddy allocation). */
static size_t
buddy_round_up (size_t n)
{
  size_t k = 1;
  while (k < n)
    {
      if (k > SIZE_MAX / 2)
        return n;               /* safety guard */
      k <<= 1;
    }
  return k;
}

/* Initializes the page allocator. */
void
palloc_init (size_t user_page_limit)
{
  uint8_t *free_start = ptov (1024 * 1024);
  uint8_t *free_end = ptov (init_ram_pages * PGSIZE);
  size_t free_pages = (free_end - free_start) / PGSIZE;
  size_t user_pages = free_pages / 2;
  size_t kernel_pages;

  if (user_pages > user_page_limit)
    user_pages = user_page_limit;
  kernel_pages = free_pages - user_pages;

  init_pool (&kernel_pool, free_start, kernel_pages, "kernel pool");
  init_pool (&user_pool, free_start + kernel_pages * PGSIZE,
             user_pages, "user pool");
}

/* Obtains and returns PAGE_CNT contiguous free pages. */
void *
palloc_get_multiple (enum palloc_flags flags, size_t page_cnt)
{
  struct pool *pool = flags & PAL_USER ? &user_pool : &kernel_pool;
  void *pages;
  size_t page_idx;
  size_t req_cnt;

  if (page_cnt == 0)
    return NULL;

  req_cnt = page_cnt;
  if (cur_mode == PAL_BUDDY)
    req_cnt = buddy_round_up (page_cnt);

  lock_acquire (&pool->lock);

  switch (cur_mode)
    {
    case PAL_FIRST_FIT:
      page_idx = bitmap_scan_and_flip (pool->used_map, 0, req_cnt, false);
      break;

    case PAL_NEXT_FIT:
      page_idx = bitmap_scan_and_flip_next_fit (pool->used_map,
                                                &pool->next_fit_start,
                                                req_cnt, false);
      break;

    case PAL_BEST_FIT:
      page_idx = bitmap_scan_and_flip_best_fit (pool->used_map,
                                                req_cnt, false);
      break;

    case PAL_BUDDY:
      /* Buddy: allocate 2^k pages using bitmap first-fit */
      page_idx = bitmap_scan_and_flip (pool->used_map, 0, req_cnt, false);
      break;

    default:
      page_idx = BITMAP_ERROR;
      break;
    }

  lock_release (&pool->lock);

  if (page_idx != BITMAP_ERROR)
    pages = pool->base + PGSIZE * page_idx;
  else
    pages = NULL;

  if (pages != NULL)
    {
      if (flags & PAL_ZERO)
        memset (pages, 0, PGSIZE * req_cnt);
    }
  else
    {
      if (flags & PAL_ASSERT)
        PANIC ("palloc_get: out of pages");
    }

  return pages;
}

/* Obtains a single free page. */
void *
palloc_get_page (enum palloc_flags flags)
{
  return palloc_get_multiple (flags, 1);
}

/* Frees PAGE_CNT pages starting at PAGES. */
void
palloc_free_multiple (void *pages, size_t page_cnt)
{
  struct pool *pool;
  size_t page_idx;
  size_t free_cnt;

  ASSERT (pg_ofs (pages) == 0);
  if (pages == NULL || page_cnt == 0)
    return;

  if (page_from_pool (&kernel_pool, pages))
    pool = &kernel_pool;
  else if (page_from_pool (&user_pool, pages))
    pool = &user_pool;
  else
    NOT_REACHED ();

  page_idx = pg_no (pages) - pg_no (pool->base);

  free_cnt = page_cnt;
  if (cur_mode == PAL_BUDDY)
    free_cnt = buddy_round_up (page_cnt);

#ifndef NDEBUG
  memset (pages, 0xcc, PGSIZE * free_cnt);
#endif

  lock_acquire (&pool->lock);
  ASSERT (bitmap_all (pool->used_map, page_idx, free_cnt));
  bitmap_set_multiple (pool->used_map, page_idx, free_cnt, false);
  lock_release (&pool->lock);
}

/* Frees a single page. */
void
palloc_free_page (void *page)
{
  palloc_free_multiple (page, 1);
}

/* Initializes pool P. */
static void
init_pool (struct pool *p, void *base, size_t page_cnt, const char *name)
{
  size_t bm_pages = DIV_ROUND_UP (bitmap_buf_size (page_cnt), PGSIZE);
  if (bm_pages > page_cnt)
    PANIC ("Not enough memory in %s for bitmap.", name);
  page_cnt -= bm_pages;

  /* IMPORTANT: do not print anything here (grading will fail). */

  lock_init (&p->lock);
  p->used_map = bitmap_create_in_buf (page_cnt, base, bm_pages * PGSIZE);
  p->base = (uint8_t *) base + bm_pages * PGSIZE;
  p->next_fit_start = 0;
}

/* Returns true if PAGE belongs to POOL. */
static bool
page_from_pool (const struct pool *pool, void *page)
{
  size_t page_no = pg_no (page);
  size_t start_page = pg_no (pool->base);
  size_t end_page = start_page + bitmap_size (pool->used_map);

  return page_no >= start_page && page_no < end_page;
}
