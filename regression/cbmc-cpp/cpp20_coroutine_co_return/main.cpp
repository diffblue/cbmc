// C++20 coroutine with co_return
#include <coroutine>
struct Task
{
  struct promise_type
  {
    Task get_return_object()
    {
      return {};
    }
    std::__n4861::suspend_never initial_suspend()
    {
      return {};
    }
    std::__n4861::suspend_never final_suspend() noexcept
    {
      return {};
    }
    void return_void()
    {
    }
    void unhandled_exception()
    {
    }
  };
};
Task coro()
{
  co_return;
}
int main()
{
  coro();
}
