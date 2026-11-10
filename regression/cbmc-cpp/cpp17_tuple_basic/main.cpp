// C++17 std::tuple
#include <tuple>
int main()
{
  auto t = std::make_tuple(1, 2.0, 'a');
  __CPROVER_assert(std::get<0>(t) == 1, "get<0>");
}
