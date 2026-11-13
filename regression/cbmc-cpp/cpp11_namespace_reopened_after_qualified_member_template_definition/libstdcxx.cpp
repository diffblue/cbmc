#include <format>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  // only including <format>: its inline std::vformat definitions must
  // convert
  int reached = 1;
  __CPROVER_assert(reached == 1, "the translation unit converts");
  __CPROVER_assert(reached == 2, "WRONG (must FAIL)");
}
