#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>

__CPROVER_bool nondet_bool();

static bool seen1[__CPROVER_constant_infinity_uint];
static bool seen2[__CPROVER_constant_infinity_uint];

typedef struct {
  bool assume;
  bool *seen;
} context_t;

__CPROVER_bool is_fresh(void **ptr, size_t size, context_t *ctx) {
  if (ctx->assume) {
    if (nondet_bool())
      return false;
    *ptr = malloc(size);
    __CPROVER_assume(*ptr);
    ctx->seen[__CPROVER_POINTER_OBJECT(*ptr)] = true;
    return true;
  } else {
    bool r_ok = __CPROVER_r_ok(*ptr, size);
    bool seen = ctx->seen[__CPROVER_POINTER_OBJECT(*ptr)];
    ctx->seen[__CPROVER_POINTER_OBJECT(*ptr)] = true;
    return r_ok && !seen;
  }
}

__CPROVER_bool ptr_equals(void **ptr, void *p, context_t *ctx) {
  if (ctx->assume) {
    if (nondet_bool())
      return false;
    *ptr = p;
    return true;
  } else {
    return p == *ptr;
  }
}

__CPROVER_bool pred(char **ptr1, char **ptr2, size_t size, context_t *ctx) {
  return (ptr_equals(ptr1, NULL, ctx) || is_fresh(ptr1, size, ctx)) &&
         (ptr_equals(ptr2, *ptr1, ctx) || ptr_equals(ptr2, NULL, ctx) ||
          is_fresh(ptr2, size, ctx) );
}

int main() {
  char *ptr1 = NULL;
  char *ptr2 = NULL;
  size_t size;

  // assume the predicate
  context_t assume_ctx = {.assume = true, .seen = seen1};
  __CPROVER_assume(pred(&ptr1, &ptr2, size, &assume_ctx));

  // check that the predicate holds
  context_t assert_ctx = {.assume = false, .seen = seen2};
  assert(pred(&ptr1, &ptr2, size, &assert_ctx));

  // in clear
  assert((ptr1 == NULL || (__CPROVER_r_ok(ptr1, size) &&
                           __CPROVER_POINTER_OFFSET(ptr1) == 0)) &&
         (ptr2 == NULL || ptr2 == ptr1 ||
          (__CPROVER_r_ok(ptr2, size) && __CPROVER_POINTER_OFFSET(ptr2) == 0) &&
              !__CPROVER_same_object(ptr1, ptr2)));

  // offsets are zero
  assert(__CPROVER_POINTER_OFFSET(ptr1) == 0);
  assert(__CPROVER_POINTER_OFFSET(ptr2) == 0);

  // this works
  int *small_array = malloc(100 * sizeof(int));
  if (small_array) {
    small_array[0] = 0;
    assert(small_array[__CPROVER_POINTER_OFFSET(ptr1)] == 0);
    assert(small_array[__CPROVER_POINTER_OFFSET(ptr2)] == 0);
  }

#ifdef BIG_ARRAY
  // this blows_up
  int *big_array = malloc(1000000 * sizeof(int));
  if (big_array) {
    big_array[0] = 0;
    assert(big_array[__CPROVER_POINTER_OFFSET(ptr1)] == 0);
    assert(big_array[__CPROVER_POINTER_OFFSET(ptr2)] == 0);
  }
#endif
}
