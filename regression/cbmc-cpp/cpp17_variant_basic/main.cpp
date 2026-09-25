// C++17 std::variant
#include <variant>
int main()
{
  std::variant<int, double> v = 42;
  __CPROVER_assert(std::holds_alternative<int>(v), "holds int");
  __CPROVER_assert(std::get<int>(v) == 42, "get int");
}
