// N5008 [variant]: std::variant holding a double.
#include <variant>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  std::variant<int, double> v = 2.5;
  __CPROVER_assert(std::holds_alternative<double>(v), "variant alternative");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
