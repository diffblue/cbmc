// N5008 [debugging.utility]: returns.
#include <debugging>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  bool present = std::is_debugger_present();
  std::breakpoint_if_debugging();
  __CPROVER_assert(present || !present, "returns");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
