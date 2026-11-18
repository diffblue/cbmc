#include <stddef.h>

int main()
{
  // A wide character constant has type wchar_t (C11 6.4.4.4p11), which must
  // match the type that the system headers use.
  __CPROVER_assert(sizeof(L'a') == sizeof(wchar_t), "width of L'a'");
  __CPROVER_assert(
    ((__typeof__(L'a'))-1 > 0) == ((wchar_t)-1 > 0), "signedness of L'a'");
  return 0;
}
