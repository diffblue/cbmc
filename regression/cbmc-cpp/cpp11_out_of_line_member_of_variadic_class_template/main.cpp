extern "C" void __CPROVER_assert(bool, const char *);
template <class R>
struct holder
{
  R (*fp)(R, R);
};
template <class R, class... A>
class function
{
  holder<R> f;

public:
  function(const function &);
  template <class F>
  function(F);
  R operator()(A... a) const
  {
    return f.fp(a...);
  }
};
// libc++'s std::function: both constructors are defined out of line; the
// copy constructor's definition comes first ([temp.mem]/1: each
// out-of-class definition matches the member template with the same
// signature)
template <class R, class... A>
function<R, A...>::function(const function &other) : f(other.f)
{
}
template <class R, class... A>
template <class F>
function<R, A...>::function(F fn) : f{fn}
{
}
int add(int a, int b)
{
  return a + b;
}
int sub(int a, int b)
{
  return a - b;
}
int main()
{
  function<int, int, int> s = sub;
  __CPROVER_assert(s(3, 4) == -1, "a second target");
  function<int, int, int> g = add;
  __CPROVER_assert(g(3, 4) == 7, "constructed from a function pointer");
  function<int, int, int> h(g);
  __CPROVER_assert(h(1, 1) == 2, "copied");
  __CPROVER_assert(g(3, 4) == 8, "WRONG (must FAIL)");
}
