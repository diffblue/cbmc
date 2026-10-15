// N5008 [dcl.fct.def.coroutine], [expr.yield], [coroutine.handle]: count()
// is a coroutine; its first resume() runs to `co_yield 1', storing 1 in the
// promise through yield_value, the second to `co_yield 2'.  The front end
// parses co_yield / co_await / co_return (cpp20_coroutines) but does not
// implement the coroutine transformation: the promise values are not
// produced and the assertion fails.
extern "C" void __CPROVER_assert(bool, const char *);
#include <coroutine>
struct gen
{
  struct promise_type
  {
    int v = 0;
    gen get_return_object()
    {
      return gen{std::coroutine_handle<promise_type>::from_promise(*this)};
    }
    std::suspend_always initial_suspend()
    {
      return {};
    }
    std::suspend_always final_suspend() noexcept
    {
      return {};
    }
    std::suspend_always yield_value(int x)
    {
      v = x;
      return {};
    }
    void return_void()
    {
    }
    void unhandled_exception()
    {
    }
  };
  std::coroutine_handle<promise_type> h;
};
gen count()
{
  co_yield 1;
  co_yield 2;
}
int main()
{
  gen g = count();
  g.h.resume();
  int a = g.h.promise().v;
  g.h.resume();
  int b = g.h.promise().v;
  g.h.destroy();
  __CPROVER_assert(a == 1 && b == 2, "coroutine");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
