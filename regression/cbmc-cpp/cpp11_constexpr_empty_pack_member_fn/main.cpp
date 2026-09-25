// N5008 [temp.variadic]/7 + [expr.const]: the instantiation of a pack
// expansion whose pack(s) expand to zero elements produces an empty list.  So
// when a (member) function template is instantiated with an *empty* type pack,
// a pack expansion appearing as a template argument in its body -- e.g.
// `Tr<U...>` for an empty `U` -- must collapse to `Tr<>` and the constexpr
// body must fold to `Tr<>::value`.
//
// This is the shape of std::tuple's constructor SFINAE constraints
// (`_TupleConstraints::__is_implicitly_constructible<>()` /
// `__is_explicitly_constructible<>()`), whose bodies expand a parameter pack
// into a trait.  CBMC instantiated such a body without collapsing the
// zero-length expansion, leaving the (now unbound) pack reference inside the
// argument; the surrounding `cpp_name` then failed to resolve and the
// expression was silently left un-type-checked, so the constexpr call folded
// to a wrong value (0/false) instead of `Tr<>::value`.
//
// A non-empty pack (`f<int>()`) already worked, so only the empty-pack case
// was affected.  `Sel<...>::v` forces the call to be folded at compile time
// (it is a non-type template argument), exercising the constant evaluation.

template <typename...>
struct Tr
{
  static constexpr int value = 42;
};

struct S
{
  template <typename... U>
  static constexpr int f()
  {
    return Tr<U...>::value;
  }
};

template <int N>
struct Sel
{
  static const int v = N;
};

int main()
{
  // f<>() instantiates with an empty U; `Tr<U...>` -> `Tr<>` -> 42.
  __CPROVER_assert(
    Sel<S::f<>()>::v == 42, "empty-pack member fn body folds to Tr<>::value");
  // non-empty control: f<int>() -> Tr<int>::value == 42.
  __CPROVER_assert(Sel<S::f<int>()>::v == 42, "one-element pack folds");
  // non-vacuity: a wrong value must FAIL.
  __CPROVER_assert(Sel<S::f<>()>::v == 0, "WRONG (must FAIL)");
  return 0;
}
