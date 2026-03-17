#include <variant>
int main()
{
  std::variant<int, double> v(42);
  __CPROVER_assert(v.index() == 0, "holds int");
}
