extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
T &&fwd(T &x)
{
  return static_cast<T &&>(x);
}
template <int I, class H>
struct leaf
{
  H value;
  // ill-formed for a reference H: must not be instantiated
  leaf() : value()
  {
  }
  template <class U>
  leaf(U &&u) : value(static_cast<U &&>(u))
  {
  }
};
template <int... I>
struct indices
{
};
template <class... T>
struct types
{
};
template <class Idx, class... T>
struct impl;
template <int... Idx, class... T>
struct impl<indices<Idx...>, T...> : leaf<Idx, T>...
{
  // libc++'s __tuple_impl: the elements given an argument are initialized
  // from it, the remaining ones (Ul/Tl) value-initialized.  With every
  // element given, the second pack expansion is over EMPTY packs and
  // expands to nothing ([temp.variadic]/7, [class.base.init]).
  template <int... Uf, class... Tf, int... Ul, class... Tl, class... U>
  impl(indices<Uf...>, types<Tf...>, indices<Ul...>, types<Tl...>, U &&...u)
    : leaf<Uf, Tf>(static_cast<U &&>(u))..., leaf<Ul, Tl>()...
  {
  }
};
int main()
{
  int i = 3;
  impl<indices<0>, int &&> t{
    indices<0>(), types<int &&>(), indices<>(), types<>(), fwd(i)};
  __CPROVER_assert(
    static_cast<leaf<0, int &&> &>(t).value == 3,
    "the reference element refers to i");
  // the other shape: no argument for the element, it is value-initialized
  impl<indices<0>, int> z{indices<>(), types<>(), indices<0>(), types<int>()};
  __CPROVER_assert(
    static_cast<leaf<0, int> &>(z).value == 0, "value-initialized element");
  __CPROVER_assert(
    static_cast<leaf<0, int &&> &>(t).value == 4, "WRONG (must FAIL)");
}
