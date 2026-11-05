// N5008 [optional]: an empty std::optional, then assigned.
#include <optional>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  std::optional<int> o;
  bool empty = !o;
  o = 3;
  __CPROVER_assert(empty && *o == 3, "optional");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
