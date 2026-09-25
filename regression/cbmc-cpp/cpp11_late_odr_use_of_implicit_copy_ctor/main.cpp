extern "C" void __CPROVER_assert(bool, const char *);
#include <set>
#include <utility>
struct loop_like
{
  std::set<int> s;
  loop_like() = default;
  template <class IS>
  explicit loop_like(IS &&instructions) : s(std::forward<IS>(instructions))
  {
  }
};
int main()
{
  std::pair<const int, loop_like> p(1, loop_like{});
  __CPROVER_assert(
    p.first == 1 && p.second.s.empty(), "pair with forwarding-ctor value");
  return 0;
}
