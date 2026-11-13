extern "C" void __CPROVER_assert(bool, const char *);
template <class>
class fn;
// N5008 [temp.mem]/1, [temp.spec.partial.member]/1: members of a class
// template partial specialization defined outside the class
template <class R, class... Args>
class fn<R(Args...)>
{
  R (*p)(Args...);

public:
  template <class F>
  fn(F f);
  R operator()(Args... args) const;
};
template <class R, class... Args>
template <class F>
fn<R(Args...)>::fn(F f) : p(f)
{
}
template <class R, class... Args>
R fn<R(Args...)>::operator()(Args... args) const
{
  return p(args...);
}
int one()
{
  return 1;
}
int twice(int x)
{
  return 2 * x;
}
int add(int x, int y)
{
  return x + y;
}
int main()
{
  fn<int()> f = one;
  fn<int(int)> g = twice;
  fn<int(int, int)> h = add;
  __CPROVER_assert(f() == 1 && g(3) == 6 && h(2, 3) == 5, "calls");
  __CPROVER_assert(f() == 0, "WRONG (must FAIL)");
  return 0;
}
