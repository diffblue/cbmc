// N5008 [temp.variadic]/4-5 + [temp.alias]/2: a MEMBER alias template whose body
// is a pack expansion over TWO parallel packs -- the alias's own parameter pack
// and the enclosing class's parameter pack -- must substitute both at the
// alias's point of use and expand them in lock-step.  This is the shape of
// libstdc++'s std::tuple constraint machinery (_TupleConstraints):
//
//   template <typename... _Types> struct _TupleConstraints {
//     template <typename... _UTypes>
//       using __constructible = __and_<is_constructible<_Types, _UTypes>...>;
//     ...
//   };
//
// KNOWNBUG: instantiating such a member alias template with a concrete pack does
// NOT fold to the correct constant -- here `chk(...)` should be a constant 3
// (each same_t<Us,Types> with Us == Types contributes 1), and g++/clang++
// compute 3, but CBMC leaves it NON-constant (all of `== 3`, `!= 3`, `== 0`
// fail, i.e. the result is unconstrained), so std::tuple's forwarding
// constructor is SFINAE-rejected and std::get<0>(std::make_tuple(1,2.0,'a'))
// reads an uninitialised member (cpp17_tuple_basic).
//
// This is DISTINCT from the (now-fixed, commit "non-type parameter pack
// arguments are expressions, not types") single-pack non-type-argument bug
// captured by cpp11_nontype_pack_member_value_args: that one was a hard
// CONVERSION ERROR ("found no match for symbol 'value'") on the SECOND non-type
// pack argument.  With that fixed, the residual defect here is specifically the
// TWO-parallel-pack MEMBER-alias body failing to fold to a constant.  The
// arguments are deduced (`chk((int)1, (double)2, (char)3)`) to avoid the
// separate qualified-nested-template-id parser bug
// (cpp11_qualified_nested_template_id_no_keyword) and the explicit-member-
// template-argument path.
//
// Flip to CORE once a two-parallel-pack member-alias body folds to the correct
// constant.
// Non-vacuity: assertion 2 ("WRONG must FAIL") must FAIL when the fix lands
// (chk() == 3), giving VERIFICATION FAILED with a genuine counterexample.

extern "C" void __CPROVER_assert(int, const char *);

template <class A, class B>
struct same_t
{
  static constexpr int v = 0;
};
template <class A>
struct same_t<A, A>
{
  static constexpr int v = 1;
};

template <int...>
struct sum_t;
template <>
struct sum_t<>
{
  static constexpr int v = 0;
};
template <int H, int... T>
struct sum_t<H, T...>
{
  static constexpr int v = H + sum_t<T...>::v;
};

template <class... Types>
struct C
{
  template <class... Us>
  using sums = sum_t<same_t<Us, Types>::v...>;
  template <class... Us>
  static constexpr int chk(Us...)
  {
    return sums<Us...>::v;
  }
};

int main()
{
  __CPROVER_assert(
    C<int, double, char>::chk((int)1, (double)2, (char)3) == 3,
    "member alias template two-parallel-pack expansion");
  __CPROVER_assert(
    C<int, double, char>::chk((int)1, (double)2, (char)3) != 3,
    "WRONG must FAIL");
  return 0;
}
