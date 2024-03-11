// Code presented in https://github.com/diffblue/cbmc/issues/7690

// clang-format off

#include <stdlib.h>
#include <stdint.h>

#if defined(_WIN32) && defined(_M_X64)
int __builtin_clzll(unsigned long long);
#define __nof_symex_objects                                                    \
  ((size_t)(1ULL << __builtin_clzll(__CPROVER_max_malloc_size)))
#else
int __builtin_clzl(unsigned long);
#define __nof_symex_objects                                                    \
  ((size_t)(1UL << __builtin_clzl(__CPROVER_max_malloc_size)))
#endif

typedef struct {
  size_t k;
  void **ptrs;
} smap_t;

void smap_init(smap_t *smap, size_t k) {
  *smap = (smap_t){
      .k = k, .ptrs = __CPROVER_allocate(__nof_symex_objects * sizeof(void *), 1)};
}

void *smap_get(smap_t *smap, void *ptr) {
  size_t id = __CPROVER_POINTER_OBJECT(ptr);
  char *sptr = smap->ptrs[id];
  if (!sptr) {
    sptr = __CPROVER_allocate(smap->k * __CPROVER_OBJECT_SIZE(ptr), 1);
    smap->ptrs[id] = sptr;
  }
  return sptr + smap->k * __CPROVER_POINTER_OFFSET(ptr);
}

typedef struct {
  uint8_t key;
  uint8_t value;
} stk_elem_t;

typedef struct {
  int8_t top;
  stk_elem_t *elems;
} stk_t;

size_t nondet_size_t();

// Creates a fresh borrow stack
stk_t *stk_new() {
  stk_t *stk = __CPROVER_allocate(sizeof(stk_t), 1);
  size_t stk_size = nondet_size_t();
  __CPROVER_assume(UINT8_MAX <= stk_size && stk_size <= UINT8_MAX);
  // works with
  // __CPROVER_assume(stk_size == UINT8_MAX);
  *stk = (stk_t){
      .top = 0,
      .elems = __CPROVER_allocate(sizeof(stk_elem_t) * stk_size, 1)};
  return stk;
}

void stk_push(stk_t *stk, uint8_t key, uint8_t value) {
  assert(stk->top < UINT8_MAX);
  stk->elems[stk->top] = (stk_elem_t){.key = key, .value = value};
  stk->top++;
}

stk_t *get_stk(smap_t *smap, void *ptr) {
  stk_t **stk_ptr = (stk_t **) smap_get(smap, ptr);
  if (!(*stk_ptr)) {
    *stk_ptr = stk_new();
  }
  return *stk_ptr;
}

typedef struct {
  int a;
  int b;
} my_struct_t;

int main() {
  smap_t smap;
  smap_init(&smap, sizeof(stk_t*));
  my_struct_t my_struct;
  stk_t *stk_a = get_stk(&smap, &(my_struct.a));
  stk_push(stk_a, 1, 1);
  stk_t *stk_b = get_stk(&smap, &(my_struct.b));
  assert(stk_b);
  stk_push(stk_b, 1, 1);
}

// clang-format on
