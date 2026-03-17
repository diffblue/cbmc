#include <tuple>

int main()
{
  auto t = std::make_tuple(1, 2.0);
  __CPROVER_assert(std::get<0>(t) == 1, "get<0>");
}
