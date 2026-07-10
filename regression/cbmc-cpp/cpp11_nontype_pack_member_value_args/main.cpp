// N5008 [temp.arg.nontype] + [temp.variadic]/4-5: the arguments matched by a
// NON-TYPE parameter pack (e.g. `template <bool...>`) are non-type template
// arguments -- converted constant expressions -- NOT types.
//
// CBMC's handling of the "extra" arguments consumed by a variadic parameter
// pack (in typecheck_template_args) treated every `ambiguous` argument as a
// TYPE and ran `typecheck_type` on it.  The parser emits an `ambiguous` node
// for a dependent qualified-id such as `is_small<T>::value` (it cannot tell a
// type-id from an expression).  The FIRST argument was handled correctly by the
// main parameter loop (which distinguishes a type parameter from a non-type
// one), but the SECOND and subsequent pack arguments went through the
// extra-argument loop and were typechecked as type-names: `value` was resolved
// as a *type* inside a freshly (and only partially) elaborated `is_small<T>`,
// failing with "found no match for symbol 'value'".
//
// Minimal trigger (no class template, no alias, no member function -- just a
// variadic non-type-parameter-pack template-id with two `Trait<T>::value`
// arguments):
//
//   template <bool...> struct all_of { static constexpr bool value = (Bs && ...); };
//   template <class T> struct is_small { static constexpr bool value = ...; };
//   all_of<is_small<char>::value, is_small<int>::value>::value;   // <-- failed
//
// A single argument (`all_of<is_small<char>::value>`) worked, and a
// fixed-arity template (`template <bool,bool> struct all_of`) worked; only the
// variadic non-type pack with >=2 such arguments was miscompiled.  This is the
// shape of libstdc++'s `__and_<is_X<...>...>` constraint packs.  g++ and clang++
// accept the program.
//
// The fix makes the extra-pack-argument loop route a NON-type parameter pack's
// arguments through the expression (non-type) path, mirroring the main loop.

extern "C" void __CPROVER_assert(int, const char *);

template <bool... Bs>
struct all_of
{
  static constexpr bool value = (Bs && ...);
};

template <class T>
struct is_small
{
  static constexpr bool value = (sizeof(T) <= 2);
};

int main()
{
  // all_of<true, true> == true.  Exercises the 2nd pack argument
  // `is_small<short>::value`, which previously failed to typecheck.
  __CPROVER_assert(
    (all_of<is_small<char>::value, is_small<short>::value>::value),
    "non-type parameter pack: two true Trait<T>::value arguments fold to true");

  // all_of<true, false> == false: the SECOND argument `is_small<int>::value`
  // must be correctly evaluated to `false` (sizeof(int) > 2), not dropped or
  // mis-elaborated.  Non-vacuity: distinguishes a correct evaluation of the
  // 2nd pack element from any stale/empty second-argument handling.
  __CPROVER_assert(
    (!all_of<is_small<char>::value, is_small<int>::value>::value),
    "non-type parameter pack: false 2nd argument makes all_of false");

  // Three arguments, to exercise the loop beyond the first extra element.
  __CPROVER_assert(
    (all_of<is_small<char>::value, is_small<short>::value, is_small<bool>::
       value>::value),
    "non-type parameter pack: three true arguments fold to true");

  return 0;
}
