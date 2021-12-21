#include <assert.h>
#include <stdlib.h>

typedef struct vect
{
  char *arr;
  size_t size;
} vect;

void resize_vec(vect *v, size_t incr)
  // clang-format off
__CPROVER_requires(
  __CPROVER_is_fresh(v, sizeof(vect)) &&
  0 < v->size && v->size <= __CPROVER_max_malloc_size &&
  0 < incr && incr < __CPROVER_max_malloc_size - v->size &&
  __CPROVER_is_fresh(v->arr, v->size)
)
__CPROVER_assigns(v->size, v->arr, __CPROVER_POINTER_OBJECT(v->arr))
__CPROVER_ensures(
  v->size == __CPROVER_old(v->size) + __CPROVER_old(incr) &&
  __CPROVER_is_fresh(v->arr, v->size)
)
// clang-format on
{
  free(v->arr);
  v->size += incr;
  v->arr = malloc(v->size);
  return;
}

void resize_vec_incr10(vect *v)
  // clang-format off
__CPROVER_requires(
  __CPROVER_is_fresh(v, sizeof(vect)) &&
  0 < v->size && v->size <= __CPROVER_max_malloc_size &&
  v->size + 10 < __CPROVER_max_malloc_size &&
  __CPROVER_is_fresh(v->arr, v->size)
)
__CPROVER_assigns(v->size)
__CPROVER_ensures(
  v->size == __CPROVER_old(v->size) + 10 &&
  __CPROVER_is_fresh(v->arr, v->size)
)
// clang-format on
{
  resize_vec(v, 10);
  return;
}
