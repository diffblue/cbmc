// Fully symbolic _Float16 remainder verification.
// Verifies |remainder(x,y)| <= |y|/2 for ALL finite _Float16 inputs.
// Completes in ~3.3s with MiniSat (16K variables, 70K clauses).
//
// See bench.c in remainderf/ for a comparison of all three approaches.

#include <assert.h>

#if defined(__GNUC__) && __GNUC__ >= 13

_Float16 __CPROVER_remainderf16(_Float16, _Float16);

int main()
{
  _Float16 pos_inf_f16 = (_Float16)(1.0 / 0.0);
  _Float16 x, y;
  __CPROVER_assume(y != (_Float16)0.0);
  __CPROVER_assume(x == x && x != pos_inf_f16 && x != -pos_inf_f16);
  __CPROVER_assume(y == y && y != pos_inf_f16 && y != -pos_inf_f16);
  _Float16 r = __CPROVER_remainderf16(x, y);
  _Float16 abs_r = r < (_Float16)0.0 ? -r : r;
  _Float16 abs_y = y < (_Float16)0.0 ? -y : y;
  assert(r == (_Float16)0.0 || abs_r <= abs_y / (_Float16)2.0);
}

#else
int main()
{
}
#endif
