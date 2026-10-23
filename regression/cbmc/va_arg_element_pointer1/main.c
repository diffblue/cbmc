#include <assert.h>

#if defined(__x86_64__)
// On x86-64, __builtin_va_list is void**, so the element type can be named and
// a pointer to an element passed to another function. va_tag extracts that
// element type, and a va_tag* parameter then has to behave like a va_list.
// Other architectures model va_list as a struct, where this does not type
// check, so the test body only applies to x86-64.
typedef typeof(((__builtin_va_list *)0)[0][0]) va_tag;

void read_arg(va_tag *args)
{
  assert(__builtin_va_arg(args, int) == 5);
}

void foo(int first, ...)
{
  va_tag args[1];
  __builtin_va_start(args, first);
  read_arg(args);
  __builtin_va_end(args);
}

int main(void)
{
  foo(0, 5);
}
#else
int main(void)
{
}
#endif
