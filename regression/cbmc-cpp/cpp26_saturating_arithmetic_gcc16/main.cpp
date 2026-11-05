// Saturation arithmetic ([numeric.sat]) as libstdc++ 16 provides it, under
// the names saturating_add and saturating_cast of a revision after N5008
// (N5008: add_sat, saturate_cast; cpp26_saturation_arithmetic).
#include <climits>
#include <numeric>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  __CPROVER_assert(
    std::saturating_add(INT_MAX, 1) == INT_MAX &&
      std::saturating_cast<unsigned char>(300) == 255,
    "saturated");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
