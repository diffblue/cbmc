// N5008 [thread.thread.constr]/6, [thread.thread.member]/3, 5: the thread
// constructor starts a thread running the function, and join waits for it.
// The standard library defines both in its compiled library.
#include <thread>
extern "C" void __CPROVER_assert(bool, const char *);
int x = 0;
int main()
{
  std::thread t([] { x = 1; });
  t.join();
  __CPROVER_assert(x == 1 && !t.joinable(), "joined");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
