// C++17 std::any
#include <any>
int main()
{
  std::any a = 42;
  __CPROVER_assert(std::any_cast<int>(a) == 42, "any value");
}
