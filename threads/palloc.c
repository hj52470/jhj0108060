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
#include "threads/list.h"

struct buddy_node {
  struct list_elem elem;
};

#define BUDDY_ALLOC_FLAG 0x80
#define BUDDY_ORDER_MASK 0x7F

struct pool
{
    struct lock lock;
    struct bitmap *used_map;
    uint8_t *base;

    size_t next_fit_start;

    bool buddy_ready;
    size_t buddy_page_cnt;
    size_t buddy_max_order;
    uint8_t *buddy_meta;                 /* order_map + nodes storage */
    uint8_t *buddy_order_map;            /* [page_cnt] */
    struct buddy_node *buddy_nodes;      /* [page_cnt] */
    struct list *buddy_free_lists;       /* [max_order + 1] */
};

static struct pool kernel_pool, user_pool;

static void init_pool (struct pool *, void *base, size_t page_cnt,
                       const char *name);
static bool page_from_pool (const struct pool *, void *page);

static enum palloc_mode cur_mode = PAL_FIRST_FIT;

void
palloc_set_mode(enum palloc_mode mode)
{
  cur_mode = mode;

  kernel_pool.next_fit_start = 0;
  user_pool.next_fit_start = 0;
}

static size_t
floor_log2_size(size_t x)
{
  size_t k = 0;
  while ((size_t)1 << (k + 1) <= x) k++;
  return k;
}

static size_t
ceil_log2_size(size_t x)
{
  size_t k = 0;
  size_t v = 1;
  while (v < x) { v <<= 1; k++; }
  return k;
}

static void
buddy_lists_init(struct pool *p, size_t page_cnt)
{
  size_t max_order = floor_log2_size(page_cnt);

  p->buddy_page_cnt = page_cnt;
  p->buddy_max_order = max_order;

  p->buddy_free_lists = (struct list *) p->buddy_meta;
  p->buddy_order_map = (uint8_t *)(p->buddy_free_lists + (max_order + 1));
  p->buddy_nodes = (struct buddy_node *)(p->buddy_order_map + page_cnt);

  for (size_t i = 0; i <= max_order; i++)
    list_init(&p->buddy_free_lists[i]);

  memset(p->buddy_order_map, 0, page_cnt);

  size_t idx = 0;
  size_t remain = page_cnt;

  while (remain > 0) {
    size_t order = floor_log2_size(remain);
    while (order > 0 && (idx & (((size_t)1 << order) - 1)) != 0)
      order--;

    size_t blk = (size_t)1 << order;

    p->buddy_order_map[idx] = (uint8_t)order;
    list_push_back(&p->buddy_free_lists[order], &p->buddy_nodes[idx].elem);

    idx += blk;
    remain -= blk;
  }

  p->buddy_ready = true;
}

static size_t
buddy_alloc_locked(struct pool *p, size_t page_cnt)
{
  if (!p->buddy_ready) return BITMAP_ERROR;
  if (page_cnt == 0) return BITMAP_ERROR;

  size_t req_order = ceil_log2_size(page_cnt);
  if (req_order > p->buddy_max_order) return BITMAP_ERROR;

  size_t order = req_order;
  while (order <= p->buddy_max_order &&
         list_empty(&p->buddy_free_lists[order]))
    order++;

  if (order > p->buddy_max_order) return BITMAP_ERROR;

  struct list_elem *e = list_pop_front(&p->buddy_free_lists[order]);
  struct buddy_node *node = list_entry(e, struct buddy_node, elem);
  size_t idx = (size_t)(node - p->buddy_nodes);

  while (order > req_order) {
    order--;
    size_t buddy = idx + ((size_t)1 << order);

    p->buddy_order_map[buddy] = (uint8_t)order;
    list_push_front(&p->buddy_free_lists[order], &p->buddy_nodes[buddy].elem);

    p->buddy_order_map[idx] = (uint8_t)order;
  }

  p->buddy_order_map[idx] = (uint8_t)(req_order | BUDDY_ALLOC_FLAG);
  bitmap_set_multiple(p->used_map, idx, (size_t)1 << req_order, true);

  return idx;
}

static void
buddy_free_locked(struct pool *p, size_t idx)
{
  uint8_t meta = p->buddy_order_map[idx];
  size_t order = (size_t)(meta & BUDDY_ORDER_MASK);

  bitmap_set_multiple(p->used_map, idx, (size_t)1 << order, false);

  while (order < p->buddy_max_order) {
    size_t buddy = idx ^ ((size_t)1 << order);
    if (buddy >= p->buddy_page_cnt) break;

    uint8_t bmeta = p->buddy_order_map[buddy];
    bool buddy_alloc = (bmeta & BUDDY_ALLOC_FLAG) != 0;
    size_t buddy_order = (size_t)(bmeta & BUDDY_ORDER_MASK);

    if (buddy_alloc || buddy_order != order) break;

    list_remove(&p->buddy_nodes[buddy].elem);

    if (buddy < idx) idx = buddy;
    order++;
  }

  p->buddy_order_map[idx] = (uint8_t)order;
  list_push_front(&p->buddy_free_lists[order], &p->buddy_nodes[idx].elem);
}

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

void *
palloc_get_multiple (enum palloc_flags flags, size_t page_cnt)
{
    struct pool *pool = flags & PAL_USER ? &user_pool : &kernel_pool;
    void *pages;
    size_t page_idx;

    if (page_cnt == 0)
        return NULL;

    lock_acquire (&pool->lock);

    switch (cur_mode) {
      case PAL_FIRST_FIT:
        page_idx = bitmap_scan_and_flip (pool->used_map, 0, page_cnt, false);
        break;

      case PAL_NEXT_FIT:
        page_idx = bitmap_scan_and_flip_next_fit(pool->used_map,
                                                 &pool->next_fit_start,
                                                 page_cnt, false);
        break;

      case PAL_BEST_FIT:
        page_idx = bitmap_scan_and_flip_best_fit(pool->used_map,
                                                 page_cnt, false);
        break;

      case PAL_BUDDY:
        page_idx = buddy_alloc_locked(pool, page_cnt);
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
                memset (pages, 0, PGSIZE * page_cnt);
        }
    else
        {
            if (flags & PAL_ASSERT)
                PANIC ("palloc_get: out of pages");
        }

    return pages;
}

void *
palloc_get_page (enum palloc_flags flags)
{
    return palloc_get_multiple (flags, 1);
}

void
palloc_free_multiple (void *pages, size_t page_cnt)
{
    struct pool *pool;
    size_t page_idx;

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

#ifndef NDEBUG
    memset (pages, 0xcc, PGSIZE * page_cnt);
#endif

    lock_acquire(&pool->lock);

    if (cur_mode == PAL_BUDDY) {
      if (pool->buddy_ready) {
        uint8_t meta = pool->buddy_order_map[page_idx];
        ASSERT((meta & BUDDY_ALLOC_FLAG) != 0);
        buddy_free_locked(pool, page_idx);
      }
    } else {
      ASSERT (bitmap_all (pool->used_map, page_idx, page_cnt));
      bitmap_set_multiple (pool->used_map, page_idx, page_cnt, false);
    }

    lock_release(&pool->lock);
}

void
palloc_free_page (void *page)
{
    palloc_free_multiple (page, 1);
}

static void
init_pool (struct pool *p, void *base, size_t page_cnt, const char *name)
{
    size_t bm_pages = DIV_ROUND_UP (bitmap_buf_size (page_cnt), PGSIZE);
    if (bm_pages > page_cnt)
        PANIC ("Not enough memory in %s for bitmap.", name);
    page_cnt -= bm_pages;

    size_t max_order = floor_log2_size(page_cnt);
    size_t buddy_lists_bytes = (max_order + 1) * sizeof(struct list);
    size_t order_map_bytes = page_cnt * sizeof(uint8_t);
    size_t nodes_bytes = page_cnt * sizeof(struct buddy_node);
    size_t buddy_meta_bytes = buddy_lists_bytes + order_map_bytes + nodes_bytes;
    size_t buddy_meta_pages = DIV_ROUND_UP(buddy_meta_bytes, PGSIZE);

    if (bm_pages + buddy_meta_pages > page_cnt + bm_pages)
      PANIC ("Not enough memory in %s for buddy metadata.", name);

    if (buddy_meta_pages > page_cnt)
      PANIC ("Not enough memory in %s for buddy metadata.", name);

    page_cnt -= buddy_meta_pages;

    /* 제출 직전 반드시 제거/비활성화 */
    printf ("%zu pages available in %s.\n", page_cnt, name);

    lock_init (&p->lock);
    p->used_map = bitmap_create_in_buf (page_cnt,
                                       base,
                                       bm_pages * PGSIZE);

    p->buddy_meta = (uint8_t *)base + bm_pages * PGSIZE;
    p->base = (uint8_t *)base + (bm_pages + buddy_meta_pages) * PGSIZE;

    p->next_fit_start = 0;
    p->buddy_ready = false;

    buddy_lists_init(p, page_cnt);
}

static bool
page_from_pool (const struct pool *pool, void *page)
{
    size_t page_no = pg_no (page);
    size_t start_page = pg_no (pool->base);
    size_t end_page = start_page + bitmap_size (pool->used_map);

    return page_no >= start_page && page_no < end_page;
}
