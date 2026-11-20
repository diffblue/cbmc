// Saturation arithmetic ([numeric.sat]) as libstdc++ 16 provides it, under
// the names saturating_add and saturating_cast of a revision after N5008
// (N5008: add_sat, saturate_cast; cpp26_saturation_arithmetic), or the
// N5008 names in earlier GCC 16 snapshots.
#include <climits>
#include <numeric>
extern "C" void __CPROVER_assert(bool, const char *);
// GCC 16 snapshots before the rename (__cpp_lib_saturation_arithmetic
// 202311L, as in CI's toolchain PPA) still have the N5008 names.
#if __cpp_lib_saturation_arithmetic >= 202603L
#  define SATURATING_ADD std::saturating_add
#  define SATURATING_CAST std::saturating_cast
#else
#  define SATURATING_ADD std::add_sat
#  define SATURATING_CAST std::saturate_cast
#endif
int main()
{
  __CPROVER_assert(
    SATURATING_ADD(INT_MAX, 1) == INT_MAX &&
      SATURATING_CAST<unsigned char>(300) == 255,
    "saturated");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
