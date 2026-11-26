extern "C" void __CPROVER_assert(bool, const char *);
#include <utility>
struct any_data
{
  void *p;
};
template <class Sig>
class fn;
template <class R, class... A>
class fn<R(A...)>
{
  typedef R (*invoker_t)(const any_data &, A &&...);
  any_data functor;
  invoker_t invoker;

public:
  template <class F>
  static R invoke(const any_data &d, A &&...args)
  {
    return (*static_cast<F *>(d.p))(std::forward<A>(args)...);
  }
  template <class F>
  explicit fn(F &f) : functor{&f}, invoker(&invoke<F>)
  {
  }
  R operator()(A... args) const
  {
    return invoker(functor, std::forward<A>(args)...);
  }
};
struct One
{
  int operator()() const
  {
    return 1;
  }
};
struct Add
{
  int operator()(int a, int b) const
  {
    return a + b;
  }
};
int main()
{
  One one;
  Add add;
  fn<int()> f0(one);
  __CPROVER_assert(f0() == 1, "zero-argument pack: operator()() body");
  fn<int(int, int)> f2(add);
  __CPROVER_assert(f2(2, 3) == 5, "two-element pack");
  return 0;
}
