#include <assert.h>

// Edge case: a const pointer to a function pointer.
// The parameter type func_ptr_t *const makes the POINTER TO the function
// pointer const; the function-pointer value it points to is itself freely
// modifiable.
typedef int (*func_ptr_t)(void);

int test_function(void)
{
  return 42;
}

void havoc_const_function_pointer(func_ptr_t *const func_ptr);

int main(void)
{
  func_ptr_t fp = test_function;
  func_ptr_t *const const_fp_ptr = &fp;

  havoc_const_function_pointer(const_fp_ptr);

  // Top-level const on the parameter does not protect the pointee: the
  // immediate pointee type (func_ptr_t) is non-const, so the havoc generator
  // reinitialises *func_ptr, i.e. fp. The function-pointer value may therefore
  // change, which is why this assertion fails.
  assert(fp == test_function);

  return 0;
}
