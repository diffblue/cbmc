#include <assert.h>
#include <limits.h>

struct S0
{
  unsigned f2 : CHAR_BIT + 1;
  int x;
};

int main()
{
  struct S0 g = {0};
  // All compilers in compiler explorer appear to agree that comma and
  // assignment expressions over bit-fields permit the use of sizeof. With GCC,
  // the result is the declared width (rounded to bytes), all others use the
  // size of the underlying type.
  // https://www.open-std.org/jtc1/sc22/wg14/www/docs/n2958.htm
  // for a discussion that this isn't actually specified (while being a
  // sizeof/typeof peculiarity)
#if defined(__GNUC__) && !defined(__INTEL_COMPILER) && !defined(__clang__)
#  define WIDTH 2
#else
#  define WIDTH sizeof(unsigned)
#endif
  _Static_assert(sizeof(++g.f2) == WIDTH, "");
  _Static_assert(sizeof(0, g.f2) == WIDTH, "");
  _Static_assert(sizeof(g.f2 = g.f2) == WIDTH, "");
  if(g.f2 <= -1)
    assert(0);
  if((g.f2 = g.f2) <= -1)
    assert(0);
}
