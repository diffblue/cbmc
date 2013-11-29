#include <assert.h>

typedef typeof(((__builtin_va_list*)0)[0][0]) __va_list_tag_type;

void my_f(int first, ...)
{
  __va_list_tag_type args[1];
  __builtin_va_start(args, first);

  int v;
  v=__builtin_va_arg(args, int);
  assert(v==2);

  __builtin_va_end(args);
}

int main()
{
  my_f(1, 2);
}
