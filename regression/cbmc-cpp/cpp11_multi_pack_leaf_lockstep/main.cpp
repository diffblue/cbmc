// N5008 [temp.variadic]/5,7: __tuple_impl's leaf-construction shape --
// a base-specifier pack expansion over TWO parallel packs
// (`leaf<Ix, Tp>...`) plus a constructor whose mem-initializer pack
// expansions cover a three-pack lockstep
// (`leaf<Uf, Tf>(static_cast<Up&&>(u))...`) and a template-pack-only
// EMPTY expansion (`leaf<Ul, Tl>()...`).  Three defects fixed: the
// base expander substituted only the FIRST referenced pack (parallel
// packs collapsed to the scalar element -- leaf<k,int> for every k of
// tuple<int,double,char>); template_mapt::apply concretized a
// >=2-element pack name before the expander ran; a mem-initializer
// expansion mentioning NO function parameter pack was left with a
// dangling `...` instead of expanding by the template packs' common
// arity (zero here -> dropped).
extern "C" void __CPROVER_assert(bool, const char *);
typedef unsigned long size_t;
template <size_t...> struct idx {};
template <class...> struct types {};
template <size_t I, class T> struct leaf
{
  T val;
  leaf() : val() {}
  explicit leaf(T &&t) : val(t) {}
};
template <class Idx, class... Tp> struct impl;
template <size_t... Ix, class... Tp>
struct impl<idx<Ix...>, Tp...> : leaf<Ix, Tp>...
{
  template <size_t... Uf, class... Tf, size_t... Ul, class... Tl, class... Up>
  explicit impl(idx<Uf...>, types<Tf...>, idx<Ul...>, types<Tl...>, Up &&... u)
    : leaf<Uf, Tf>(static_cast<Up &&>(u))..., leaf<Ul, Tl>()...
  {
  }
};
int main()
{
  impl<idx<0, 1, 2>, int, double, char> t(
    idx<0, 1, 2>(), types<int, double, char>(), idx<>(), types<>(), 1, 2.0,
    'a');
  __CPROVER_assert(static_cast<leaf<0, int> &>(t).val == 1, "leaf0");
  __CPROVER_assert(static_cast<leaf<1, double> &>(t).val == 2.0, "leaf1");
  __CPROVER_assert(static_cast<leaf<2, char> &>(t).val == 'a', "leaf2");
  return 0;
}
