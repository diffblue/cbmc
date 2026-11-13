#include <algorithm>
#include <cstdint>
extern "C" void __CPROVER_assert(bool, const char *);
inline constexpr uint32_t entries[4] = {10, 20, 30, 40};
constexpr int estimated(const uint32_t v) noexcept
{
  if(v > 100) [[unlikely]]
    return 1;
  long i = std::ranges::upper_bound(entries, v) - entries;
  return static_cast<int>(i);
}
int main()
{
  __CPROVER_assert(
    estimated(25) == 2, "ranges::upper_bound on a built-in array");
  __CPROVER_assert(estimated(5) == 0, "before first");
  __CPROVER_assert(estimated(25) == 3, "WRONG (must FAIL)");
}
