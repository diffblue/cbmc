#include <utility>
#include <vector>
extern "C" void __CPROVER_assert(bool, const char *);
// no default constructor
struct symbolish
{
  int x;
  symbolish(int v) : x(v)
  {
  }
};
int main()
{
  std::vector<std::pair<symbolish, unsigned long>> v;
  v.emplace_back(symbolish{1}, 2ul);
  __CPROVER_assert(v.size() == 1, "one element");
  __CPROVER_assert(v[0].first.x == 1 && v[0].second == 2, "its value");
  __CPROVER_assert(v[0].second == 3, "WRONG (must FAIL)");
}
