// N5008 [temp.variadic]/4-5 + [temp.res] (two-phase): a pack expansion whose
// pattern is a NON-TYPE value dependent on the pack -- `Trait<Us>::value...` --
// appearing as the template-argument list of a template-id in a FUNCTION
// TEMPLATE's body must be re-instantiated with the concrete pack when the
// function template is instantiated, and expand to one argument per element.
//
// KNOWNBUG: CBMC resolves `box<sz<Us>::v...>` (the `::v` non-type value form)
// abstractly at the point the function template `chk` is DEFINED (its pack `Us`
// still unbound) and does NOT re-instantiate it concretely when `chk<char,char>`
// is instantiated -- only an abstract `box<Non_Type0>` is ever produced, so
// `box<...>::n` (== `sizeof...(Vs)`) is left unconstrained instead of 2.
//
// Decisive contrast (both are dependent template-ids in the same body):
//   box<sz<Us>...>::n        // TYPE-id pattern    -> re-instantiates, n == 2 (OK)
//   box<sz<Us>::v...>::n     // ::value pattern    -> stays abstract, n unconstrained
// A bare pack (`box<Us...>::n`) and a nested type-id (`box<sz<Us>...>::n`) both
// re-instantiate correctly; only the non-type `::value` pack expansion fails.
// No class template or alias is needed (an earlier reproducer used a member
// alias and `sizeof(Us)...`, which added confounds); a free function template
// with a `Trait<Us>::value...` argument is the minimal trigger.  g++/clang++
// compute 2.
//
// This is the residual blocker beneath the (separately fixed) two-parallel-pack
// member-alias expansion (cpp11_alias_template_parallel_pack) and for
// std::tuple's _TupleConstraints (`__and_<is_X<_Types,_UTypes>...>::value`,
// which is exactly a `Trait<...>::value` non-type pack instantiated with a
// forwarded pack).
//
// Flip to CORE once a `Trait<Us>::value...` non-type pack expansion in a
// function-template body is re-instantiated concretely at the function
// template's point of instantiation.
// Non-vacuity: assertion 2 ("WRONG must FAIL") must FAIL when the fix lands
// (the count is exactly 2).

extern "C" void __CPROVER_assert(int, const char *);

template <class T>
struct sz
{
  static constexpr unsigned v = sizeof(T);
};

template <unsigned... Vs>
struct box
{
  static constexpr unsigned n = sizeof...(Vs);
};

template <class... Us>
constexpr unsigned chk(Us...)
{
  return box<sz<Us>::v...>::n;
}

int main()
{
  __CPROVER_assert(
    chk((char)1, (char)2) == 2,
    "non-type value pack Trait<Us>::value... expands to 2 elements");
  __CPROVER_assert(chk((char)1, (char)2) != 2, "WRONG must FAIL");
  return 0;
}
