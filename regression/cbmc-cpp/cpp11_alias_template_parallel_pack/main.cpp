// N5008 [temp.variadic]/4-5 + [temp.alias]/2: a MEMBER alias template whose body
// is a pack expansion over TWO parallel packs -- the alias's own parameter pack
// and the enclosing class's parameter pack -- must substitute both at the
// alias's point of use and expand them in lock-step.  This is exactly the shape
// of libstdc++'s std::tuple constraint machinery (_TupleConstraints):
//
//   template <typename... _Types> struct _TupleConstraints {
//     template <typename... _UTypes>
//       using __constructible = __and_<is_constructible<_Types, _UTypes>...>;
//     ...
//   };
//
// where __and_ is a TYPE parameter pack template and the constraint is read as
// `__constructible<_UTypes...>::value`.
//
// Regression history: this mis-expanded because the member alias template's own
// pack was expanded (by the enclosing class pack alone) during class
// instantiation, leaving the alias's own pack dangling; fixed by deferring the
// own-pack expansion to the alias's point of use ("defer a member alias
// template's own-pack expansion during class instantiation").  With that (and
// the combined-candidate / non-type-pack-argument fixes) the two-parallel-pack
// member alias now expands correctly.
//
// Non-vacuity: `chk` is true exactly when every `Us` equals the corresponding
// `Types` (matched), and false otherwise (mismatched) -- so the assertions
// distinguish a correct lock-step pairing from any collapsed/one-pack
// expansion.  g++/clang++ agree.

extern "C" void __CPROVER_assert(int, const char *);

template <class...>
struct and_;
template <>
struct and_<>
{
  static constexpr bool value = true;
};
template <class H, class... T>
struct and_<H, T...>
{
  static constexpr bool value = H::value && and_<T...>::value;
};

template <class A, class B>
struct is_same
{
  static constexpr bool value = false;
};
template <class A>
struct is_same<A, A>
{
  static constexpr bool value = true;
};

template <class... Types>
struct C
{
  // Two parallel packs: the alias's own `Us` and the enclosing class's `Types`.
  template <class... Us>
  using all_same = and_<is_same<Us, Types>...>;
  template <class... Us>
  static constexpr bool chk(Us...)
  {
    return all_same<Us...>::value;
  }
};

int main()
{
  // Matched: each Us == the corresponding Types -> all_same is true.
  __CPROVER_assert(
    C<int, double, char>::chk((int)1, (double)2, (char)3),
    "two-parallel-pack member alias: matched packs -> true");

  // Mismatched: the packs pair up but differ -> all_same is false.
  __CPROVER_assert(
    !C<int, char>::chk((char)1, (int)2),
    "two-parallel-pack member alias: mismatched packs -> false");

  return 0;
}
