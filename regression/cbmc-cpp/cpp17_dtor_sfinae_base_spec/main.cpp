// N5008 [temp.inst]/1-3 + [dcl.type.decltype] + [temp.deduct]/8: the base
// specifier `impl<T>::type` names the result of the classic
// destructibility probe -- `decltype(test<T>(0))` selects the
// bool_c<true> overload for class type S because
// `decltype(declval<T&>().~T())` is well-formed.  Everything below is
// valid C++; g++ and clang++ accept it, and at runtime trait_v<S> is
// false and `engaged` is false.
//
// KNOWNBUG: resolving that decltype-SFINAE base specifier fails when the
// class is elaborated inside a NESTED instantiation context (here: the
// default template argument `bool = trait_v<T>` of the payload member of
// base_<S>, itself instantiated as opt<S>'s base).  The per-base
// recovery then drops safe<S>'s base, and_'s base (which needs
// safe<S>::value), and finally opt<S>'s base_ -- leaving opt<S> with no
// members, so has_value() reads nondet.  The same chain, elaborated
// directly at user level, resolves fine.
//
// This is the exact skeleton of libstdc++'s std::optional<std::string>
// residual (cpp17_optional_string): __do_is_destructible_impl::__test /
// __is_destructible_impl<...>::type / __is_destructible_safe /
// __and_<...> / _Optional_payload's `bool = is_trivially_destructible`
// default argument / _Optional_base dropped.  Reduced with cvise on
// cbmc-preprocessed source plus hand-minimization.  Flip to CORE (and
// cpp17_optional_string with it) when the nested-context decltype-SFINAE
// base specifier resolves.
extern "C" void __CPROVER_assert(bool, const char *);

template <bool V>
struct bool_c
{
  static constexpr bool value = V;
};
template <bool, typename T, typename F>
struct cond
{
  typedef T type;
};
template <typename T, typename F>
struct cond<false, T, F>
{
  typedef F type;
};
// libstdc++ __and_ shape: the base NEEDS B1::value
template <typename B1, typename B2>
struct and_ : cond<B1::value, B2, B1>::type
{
};
template <typename T>
T &&declval();
// the classic destructibility probe (__do_is_destructible_impl)
struct do_impl
{
  template <typename T, typename = decltype(declval<T &>().~T())>
  static bool_c<true> test(int);
  template <typename>
  static bool_c<false> test(...);
};
template <typename T>
struct impl : do_impl
{
  typedef decltype(test<T>(0)) type;
};
template <typename T>
struct safe : impl<T>::type
{
};
struct S
{
  int x;
};
template <typename T>
constexpr bool trait_v = and_<safe<T>, bool_c<false>>::value;
// _Optional_payload shape: trait in a default template argument
template <typename T, bool = trait_v<T>>
struct payload
{
  bool engaged = false;
};
// _Optional_base shape
template <typename T>
struct base_
{
  payload<T> p;
  bool is_engaged()
  {
    return p.engaged;
  }
};
// optional shape
template <typename T>
struct opt : base_<T>
{
  bool has_value()
  {
    return this->is_engaged();
  }
};

int main()
{
  opt<S> o;
  __CPROVER_assert(!o.has_value(), "empty");
  return 0;
}
