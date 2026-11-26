// N5008 [tuple]: std::make_tuple and std::get.
#include <tuple>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  auto t = std::make_tuple(1, 2.5, 'c');
  __CPROVER_assert(std::get<0>(t) == 1 && std::get<2>(t) == 'c', "tuple get");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
