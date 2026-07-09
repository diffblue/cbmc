// N5008 [temp.variadic]/4-5 + [temp.alias]: a member alias template whose body
// is a pack expansion over TWO parallel packs -- the alias's own parameter pack
// and the enclosing class's parameter pack -- must expand them in lock-step.
// This is the shape of libstdc++'s std::tuple constraint machinery
// (_TupleConstraints):
//
//   template <typename... _Types> struct _TupleConstraints {
//     template <typename... _UTypes>
//       using __constructible = __and_<is_constructible<_Types, _UTypes>...>;
//     template <typename... _UTypes>
//       using __convertible  = __and_<is_convertible<_UTypes, _Types>...>;
//     ...
//   };
//
// KNOWNBUG: when such a member alias template is instantiated, its own parameter
// pack (here `Us`) is not bound -- the pack `Us...` passed as the alias's
// argument list (`sums<Us...>`) resolves to ZERO arguments, so only the
// enclosing class pack (`Types`) is bound.  The two-parallel-pack body then
// expands against only one pack (the other reference is left unresolved) and the
// alias evaluates to the wrong result ("found no match for symbol 'v'").  This
// is why std::make_tuple's forwarding constructor is SFINAE-rejected
// (_ImplicitCtor<...> -> __is_implicitly_constructible<...>() spuriously false),
// so the tuple's element-storing constructor never gets a body and
// std::get<0>(std::make_tuple(1,2.0,'a')) reads an uninitialised member
// (cpp17_tuple_basic).
//
// g++ computes chk() == 3 (each same_t<Us,Types> with Us==Types is 1).
// Flip to CORE once a member alias template's own parameter pack is bound and a
// two-parallel-pack body expands in lock-step.
// assertion "WRONG" must FAIL (non-vacuity).

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
  static constexpr int chk()
  {
    return sums<Us...>::v;
  }
};

int main()
{
  __CPROVER_assert(
    C<int, double, char>::chk<int, double, char>() == 3,
    "member alias template two-parallel-pack expansion");
  __CPROVER_assert(
    C<int, double, char>::chk<int, double, char>() != 3, "WRONG must FAIL");
  return 0;
}
