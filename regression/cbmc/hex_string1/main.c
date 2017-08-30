#include <assert.h>

#define static_assert(x) ((struct { char some[(x)?1:-1]; }*)0)

int main()
{
  static_assert('\xe8'==(char)0xe8);
  static_assert(sizeof("abc")==4);
  static_assert(sizeof("\u0201")==3);
  static_assert(sizeof("\xe8")==2);
  static_assert(sizeof("\u0201\xe8")==4);

  if("\xe8"[0]!=(char)0xe8)
    assert(0);
  return 0;
}
