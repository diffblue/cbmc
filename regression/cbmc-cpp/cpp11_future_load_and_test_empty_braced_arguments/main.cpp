#include <future>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  // only including <future>: its inline members must convert
  int reached = 1;
  __CPROVER_assert(reached == 1, "future header converts");
  __CPROVER_assert(reached == 2, "WRONG (must FAIL)");
}
