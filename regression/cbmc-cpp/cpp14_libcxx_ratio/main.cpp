// libc++ std::ratio: constexpr static members with recursive
// template metafunctions (__static_gcd) fail to evaluate.
// The template parameter substitution works for direct references
// (e.g., __static_abs<_Num> → __static_abs<1>) but fails for
// expressions inside template arguments (e.g., _Xp % _Yp in
// __static_gcd<_Yp, _Xp % _Yp>).
#include <ratio>
static_assert(std::ratio<1>::num == 1, "ratio num");
int main()
{
}
