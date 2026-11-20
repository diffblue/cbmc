// N5008 [temp.deduct.general]/5, [over.ics.user]: `fn<up<base>> f = 0'
// copy-initializes from 0 through fn's constructor template, whose default
// template argument asks whether up<derived> converts to up<base>.  That
// conversion uses up's converting constructor template, whose own default
// template argument asks whether del<derived> converts to del<base> -- with
// del's converting constructor template.  Each nested query is a separate
// conversion sequence.  The front end allowed one nested constructor
// template conversion only, the innermost one failed, and no constructor
// of fn was viable: "found no match for symbol 'fn'" (the shape of
// std::function<unique_ptr<B>()> from a lambda returning unique_ptr<D>,
// with default_delete; CBMC's own goto-harness generator factory,
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
int main()
{
  fn<up<base>> f = 0;
  __CPROVER_assert(f.made == 2, "constructor template viable");
  up<base> u = up<derived>();
  __CPROVER_assert(u.tag == 1, "converting constructor");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
