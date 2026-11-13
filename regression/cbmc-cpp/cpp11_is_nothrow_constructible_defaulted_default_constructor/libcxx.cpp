#include <mutex>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  std::mutex m;
  m.lock();
  m.unlock();
  __CPROVER_assert(true, "mutex used");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
