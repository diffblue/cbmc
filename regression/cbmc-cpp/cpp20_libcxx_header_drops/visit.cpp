#include <variant>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  std::variant<int, char> v = 3;
  struct F
  {
    int operator()(int x) const
    {
      return x;
    }
    int operator()(char c) const
    {
      return c;
    }
  };
  int r = std::visit(F{}, v);
  __CPROVER_assert(r >= 3, "visit");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
