#include <assert.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>

bool dummy_for_definitions(int *n)
{
  assert(__CPROVER_is_fresh(&n, sizeof(int)));
  int *x = malloc(sizeof(int));
}

bool ptr_ok(int *x)
{
  return *x < 5;
}

/*
	Here are the meanings of the predicates: 

static _Bool __foo_memory_map[__CPROVER_constant_infinity_uint]; 

bool __foo_requires_is_fresh(void **elem, size_t size) {
	*elem = malloc(size);
	if (!*elem || (__foo_memory_map[__CPROVER_POINTER_OBJECT(*elem)] != 0)) return false;

	__foo_memory_map[__CPROVER_POINTER_OBJECT(*elem)] = 1;
	return true;
}

bool __foo_ensures_is_fresh(void *elem, size_t size) {
	bool ok = (__foo_memory_map[__CPROVER_POINTER_OBJECT(elem)] == 0 && 
		  	   __CPROVER_r_ok(elem, size));
	__foo_memory_map[__CPROVER_POINTER_OBJECT(elem)] = 1;
	return ok;
}


_Bool __call_foo_requires_is_fresh(void *elem, size_t size) {
	_Bool r_ok = __CPROVER_r_ok(elem, size);
	if (!__CPROVER_r_ok(elem, size) || 
	    __foo_memory_map[__CPROVER_POINTER_OBJECT(elem)]) return 0;
	__foo_memory_map[__CPROVER_POINTER_OBJECT(elem)] = 1;
	return 1;
}

// In the calling context, we assume freshness means new 
// allocation from within the function.
bool __call_foo_ensures_is_fresh(void **elem, size_t size) {
	*elem = malloc(size);
	return (*elem != NULL);
}
*/

bool return_ok(int ret_value, int *x)
{
  int a;
  a = *x;
  return ret_value == *x + 5;
}

// The 'ensures' __CPROVER_is_fresh test is unnecessary, but left in just to test the function is working correctly.
// If you remove the negation, the program will fail, because 'x' is not fresh.

int foo(int *x, int y) __CPROVER_assigns(*x)
  __CPROVER_requires(__CPROVER_is_fresh(x, sizeof(int)) && *x > 0 && ptr_ok(x))
    __CPROVER_ensures(
      !ptr_ok(x) && !__CPROVER_is_fresh(x, sizeof(int)) &&
      return_ok(__CPROVER_return_value, x))
{
  *x = *x + 4;
  int y = *x + 5;
  return *x + 5;
}

int main()
{
  int *n = malloc(sizeof(int));
  assert(__CPROVER_r_ok(n, sizeof(int)));
  *n = 3;
  int o = foo(n, 10);
  assert(o >= 10 && o == *n + 5);
  return 0;
}
