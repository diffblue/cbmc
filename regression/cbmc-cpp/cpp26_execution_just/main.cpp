// N5008 [exec.just], [exec.sync.wait]: sync_wait of just.
#include <execution>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  auto [v] = std::this_thread::sync_wait(std::execution::just(3)).value();
  __CPROVER_assert(v == 3, "sync_wait of just");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
