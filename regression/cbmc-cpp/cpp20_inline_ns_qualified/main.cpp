// Inline namespace qualified lookup: std::suspend_never
#include <coroutine>
int main()
{
  std::suspend_never sn;
  __CPROVER_assert(sn.await_ready(), "suspend_never");
}
