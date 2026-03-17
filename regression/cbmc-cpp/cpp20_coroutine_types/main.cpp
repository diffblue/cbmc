// C++20 coroutine types from <coroutine>
#include <coroutine>
int main()
{
  std::suspend_never sn;
  __CPROVER_assert(sn.await_ready(), "suspend_never");
}
