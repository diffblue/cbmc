// N5008 [numeric.sat.func], [numeric.sat.cast]: saturated.
#include <climits>
#include <numeric>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  __CPROVER_assert(
    std::add_sat(INT_MAX, 1) == INT_MAX &&
      std::saturate_cast<unsigned char>(300) == 255,
    "saturated");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
