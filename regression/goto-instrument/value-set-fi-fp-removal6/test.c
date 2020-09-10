#include <assert.h>

typedef void (*fp_t)(void);

void f()
{
}

void g()
{
}

int main(void)
{
  fp_t fp = f;
  fp_t decoy_fp = g;
  fp_t *ptr_to_func_ptr = &fp; // a pointer to a function pointer
  (*ptr_to_func_ptr)();
}
