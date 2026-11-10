#include <tuple>
#include <utility>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  int x = 7;
  std::tuple<int &&> a(std::move(x));
  std::tuple<int> b(std::move(a));
  __CPROVER_assert(std::get<0>(b) == 7, "converted");
  std::tuple<int> c(std::forward_as_tuple(3));
  __CPROVER_assert(std::get<0>(c) == 3, "from forward_as_tuple");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
