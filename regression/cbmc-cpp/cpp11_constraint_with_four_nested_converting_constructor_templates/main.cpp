// N5008 [temp.deduct.general]/5, [over.ics.user]: the braced argument
// `{1, 0}' of take's duo<int, fn<up<base>>> parameter uses duo's
// constructor template, whose constraint constructs fn from the int, whose
// constraint converts up<derived> to up<base>, whose constraint converts
// del<derived> to del<base>: four nested constructor-template conversions,
// each a separate conversion sequence.  The front end allowed two nested
// levels and found no constructor of duo (the shape of std::map's
// initializer list of std::pair<K, std::function<unique_ptr<B>()>> with
// lambdas returning unique_ptr<D>; CBMC's own path_storage.cpp,
// dog-fooding).
extern "C" void __CPROVER_assert(bool, const char *);
template <bool B, class T = void>
struct en
{
  using type = T;
};
template <class T>
struct en<false, T>
{
};
struct base
{
  int v = 1;
};
struct derived : base
{
};
template <class T>
struct del
{
  del() = default;
  template <class U, class = typename en<__is_convertible(U *, T *)>::type>
  del(const del<U> &)
  {
  }
};
template <class T, class D = del<T>>
struct up
{
  int tag = 0;
  up() = default;
  template <class U, class E, class = typename en<__is_convertible(E, D)>::type>
  up(up<U, E> &&o) : tag(o.tag + 1)
  {
  }
};
template <typename R>
struct fn
{
  int made = 0;
  template <
    typename F,
    typename = typename en<__is_convertible(up<derived>, R)>::type>
  fn(F x) : made(x + 2)
  {
  }
};
// a pair-like class whose constructor template is constrained on fn
template <class A, class B>
struct duo
{
  A a;
  B b;
  template <
    class U,
    class V,
    class = typename en<__is_constructible(B, V)>::type>
  duo(U &&u, V &&v) : a(u), b(v)
  {
  }
};
int take(duo<int, fn<up<base>>> d)
{
  return d.a + d.b.made;
}
int main()
{
  fn<up<base>> f = 0;
  __CPROVER_assert(f.made == 2, "constructor template viable");
  up<base> u = up<derived>();
  __CPROVER_assert(u.tag == 1, "converting constructor");
  // a braced argument: duo's constraint constructs fn, whose constraint
  // converts up<derived>, whose constraint converts del<derived>
  __CPROVER_assert(take({1, 0}) == 3, "four nested levels");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
