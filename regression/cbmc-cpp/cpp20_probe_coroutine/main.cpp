// N5008 [dcl.fct.def.coroutine], [expr.yield]: the yielded value.
#include <coroutine>
extern "C" void __CPROVER_assert(bool, const char *);
struct G
{
  struct promise_type
  {
    int v = 0;
    G get_return_object()
    {
      return G{std::coroutine_handle<promise_type>::from_promise(*this)};
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
G gen()
{
  co_yield 7;
}
int main()
{
  G g = gen();
  g.h.resume();
  int v = g.h.promise().v;
  g.h.destroy();
  __CPROVER_assert(v == 7, "the yielded value");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
