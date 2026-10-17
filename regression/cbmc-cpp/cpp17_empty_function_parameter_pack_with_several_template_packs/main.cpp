// N5008 [temp.variadic]/7: an expansion over an empty pack has no
// elements.  impl<Js..., Ls...> is instantiated with Js = {0, 1, 2} and
// Ls = {}: its function parameter pack ls has no parameters, and in
// `sum(impl<int>(seq<Js>{}, ls...)...)' only the nested `ls...' vanishes
// -- the outer expansion is over Js ([temp.variadic]/5: a pack is expanded
// by the innermost expansion containing it).  With several template packs
// the empty function parameter pack was left in place ("symbol 'ls' is
// unknown"), and removing it took the outer expansion with it.  libc++'s
// __base::__make_fmatrix_impl (std::visit) has this shape.
extern "C" void __CPROVER_assert(bool, const char *);
template <unsigned long... I>
struct seq
{
};
template <class... Fs>
int sum(Fs... fs)
{
  return (0 + ... + fs);
}
template <class... Ts>
struct pack
{
  static constexpr unsigned long size()
  {
    return sizeof...(Ts);
  }
};
struct base
{
  template <class, unsigned long... Is>
  static auto impl(seq<Is...>)
  {
    return (10 + ... + Is);
  }
  template <unsigned long... Js, class... Ls>
  static int impl(seq<>, seq<Js...>, Ls... ls)
  {
    return sum(impl<int>(seq<Js>{}, ls...)...);
  }
  template <class, class... Vs>
  static int make()
  {
    return impl(seq<>{}, seq<0, 1, 2>{});
  }
  template <class... Vs>
  static int visit(Vs...)
  {
    return make<int, Vs...>();
  }
};
int main()
{
  __CPROVER_assert(base::visit(pack<char>{}) == 33, "matrix");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
