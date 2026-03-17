// C++11 std::initializer_list basic usage
#include <initializer_list>

int main()
{
  auto il = {1, 2, 3};
  __CPROVER_assert(il.size() == 3, "initializer_list size");
  return 0;
}
