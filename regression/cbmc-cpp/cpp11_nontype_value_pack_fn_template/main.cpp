// N5008 [expr.sizeof]/5 + [temp.variadic]/8: `sizeof...(P)` counts the elements
// of the pack P, independently of whether P is a type or a NON-type parameter
// pack.
//
// Regression: CBMC's parser stored a non-type parameter pack's name (which does
// not parse as a type-id, e.g. `template<unsigned... Vs>`) as the OPERAND of the
// `sizeof...` expression rather than in ID_type_arg.  An operand is type-checked
// as a value expression before typecheck_expr_sizeof's `#sizeof_pack`
// pack-counting path runs, collapsing the query to a stray constant -- so
// `box<1,1>::n` (with `n = sizeof...(Vs)`) did not evaluate to 2 (it was wrong
// for every arity).  A TYPE parameter pack (`template<class... Vs>`) was
// unaffected because its name parses as a type-id and goes through ID_type_arg.
//
// The fix stores the non-type pack's name in ID_type_arg as well, so both forms
// take the pack-counting path.  This also surfaced through a pack expansion
// whose pattern is a non-type value `Trait<Us>::value...` forwarded into a
// function template (`box<sz<Us>::v...>::n` in `chk`): the count was wrong.
// g++/clang++ accept the program and compute the shown values.

extern "C" void __CPROVER_assert(int, const char *);

template <unsigned... Vs>
struct box
{
  static constexpr unsigned n = sizeof...(Vs);
};

template <class T>
struct sz
{
  static constexpr unsigned v = sizeof(T);
};

template <class... Us>
constexpr unsigned chk(Us...)
{
  return box<sz<Us>::v...>::n;
}

int main()
{
  // Direct non-type parameter pack sizeof...: count depends on arity, so these
  // three assertions are non-vacuous (a broken sizeof... cannot satisfy all).
  __CPROVER_assert(box<1>::n == 1, "sizeof... of a 1-element non-type pack");
  __CPROVER_assert(box<1, 1>::n == 2, "sizeof... of a 2-element non-type pack");
  __CPROVER_assert(
    box<1, 2, 3>::n == 3, "sizeof... of a 3-element non-type pack");

  // A non-type value pack expansion `sz<Us>::v...` forwarded into a function
  // template, then counted with sizeof...: two `char` arguments -> 2 elements.
  __CPROVER_assert(
    chk((char)1, (char)2) == 2,
    "non-type value pack Trait<Us>::value... forwarded and counted");

  return 0;
}
