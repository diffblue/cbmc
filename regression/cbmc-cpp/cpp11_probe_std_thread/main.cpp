// N5008 [thread.thread.constr], [thread.thread.member]: the thread ran before
// join returned.
#include <thread>
extern "C" void __CPROVER_assert(bool, const char *);
int x = 0;
int main()
{
  std::thread t([] { x = 1; });
  t.join();
  __CPROVER_assert(x == 1, "the thread ran before join returned");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
