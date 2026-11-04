// _Float16 exhaustive verification: |fmod(x,y)| < |y|.
// (Coq: fmod_then_remainder — integer remainder bound)

#include <assert.h>

#if defined(__GNUC__) && __GNUC__ >= 13

_Float16 __CPROVER_fmodf16(_Float16, _Float16);

int main()
{
  _Float16 x, y;
  __CPROVER_assume(
    x == x && x != (_Float16)(1.0 / 0.0) && x != -(_Float16)(1.0 / 0.0));
  __CPROVER_assume(
    y == y && y != (_Float16)(1.0 / 0.0) && y != -(_Float16)(1.0 / 0.0));
  __CPROVER_assume(y != (_Float16)0.0);
  _Float16 r = __CPROVER_fmodf16(x, y);
  _Float16 abs_r = r < (_Float16)0.0 ? -r : r;
  _Float16 abs_y = y < (_Float16)0.0 ? -y : y;
  assert(r == (_Float16)0.0 || abs_r < abs_y);
}

#else
int main()
{
}
#endif
