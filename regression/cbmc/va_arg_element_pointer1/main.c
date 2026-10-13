#include <assert.h>

// On x86_64 (glibc), __builtin_va_list is void**.
// va_tag extracts the element type of __builtin_va_list, so a
// va_tag* parameter behaves identically to a va_list parameter
// when passed by pointer.
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
