#include <ctype.h>

int __CPROVER_uninterpreted_tolower(int);

// clang-format off
void tl1(char *dst, __CPROVER_size_t len)
  __CPROVER_requires(__CPROVER_is_fresh(dst, len))
  __CPROVER_assigns(__CPROVER_object_whole(dst))
  __CPROVER_ensures(__CPROVER_forall {
    int i;
    (0 <= i && i < len) ==> dst[i % len] ==
      __CPROVER_uninterpreted_tolower(__CPROVER_old(dst[i % len]))
  });
// clang-format on

void tl1(char *dst, __CPROVER_size_t len)
{
  for(__CPROVER_size_t i = 0; i < len; i++)
  {
    dst[i] = tolower(dst[i]);
  }
}

int main()
{
  char st[8] = "HELLOROD";
  tl1(st, 8);
}
