// N5008 [expr.prim.fold]/2: `(100 + ... + Is)' over Is = {1} is 100 + 1.
// Is is the third template parameter pack of a constexpr static member
// function template; libc++'s __base::__make_fmatrix_impl (std::visit)
// folds there.  The fold was left to the C type-checker's fallback,
// which made it `true'.
extern "C" void __CPROVER_assert(bool, const char *);

template <unsigned long... I>
struct seq
{
};

template <class... Fs>
constexpr int sum(Fs... fs)
{
  return (0 + ... + fs);
}

struct base
{
  template <class F, class... Vs, unsigned long... Is>
  static constexpr int impl(seq<Is...>)
  {
    return (100 + ... + Is) * 10 + (int)sizeof...(Vs);
  }

  template <class F, class... Vs, unsigned long... Is, unsigned long... Js>
  static constexpr int impl2(seq<Is...>, seq<Js...>)
  {
    return sum(impl<F, Vs...>(seq<Is..., Js>{})...);
  }
};

int main()
{
  __CPROVER_assert(base::impl<int, char>(seq<1>{}) == 1011, "direct");
  // (100 + 0) * 10 + 1 + (100 + 1) * 10 + 1 + (100 + 2) * 10 + 1
  __CPROVER_assert(
    base::impl2<int, char>(seq<>{}, seq<0, 1, 2>{}) == 3033, "nested");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
