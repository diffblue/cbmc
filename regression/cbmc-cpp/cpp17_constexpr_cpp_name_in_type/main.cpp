// Regression for the constexpr-eager-convert "cpp_name in type field"
// blind spot in `cpp_typecheckt::do_typecheck_side_effect_function_call`.
//
// When a constexpr function is invoked with constant arguments, CBMC's
// constexpr inliner substitutes the body's expressions into the
// caller's scope.  Before substitution, an "eager convert" path runs
// `convert_function` on the callee's body so unresolved cpp_names are
// type-checked in the body's own (class) scope first.  The trigger
// for this eager path is "the body's irept tree contains any
// `ID_cpp_name`".  The previous implementation used
// `exprt::visit_pre`, which walks `operands()` only — it does not
// descend into the `type` field or other named-sub fields of inner
// expressions.
//
// As a result, a `cpp_name` appearing as the *type* of a sub-
// expression (e.g., the target type of a `static_cast<int_type>(...)`
// inside the body) was invisible to the trigger.  The eager-convert
// path was skipped, the body remained partially resolved, and the
// inliner then substituted the unresolved `int_type` cpp_name into
// the caller's scope — surfacing the spurious diagnostic
//
//   invalid implicit conversion from '<<type:cpp_name>>' to 'signed int'
//
// even though `int_type` is a perfectly resolvable typedef in the
// callee's class scope.
//
// Visible symptom: any translation unit that includes <sstream> in
// CBMC's own source (10 files in the dog-food set after the
// inline-class-member-recovery fix) failed with this exact
// diagnostic, originating from
//
//   /usr/include/c++/13/bits/char_traits.h line 467 function eof:
//   { return static_cast<int_type>(_GLIBCXX_STDIO_EOF); }
//
// This pattern maps directly to:
//   namespace synth {
//     template<typename T> struct char_traits { /* no int_type */ };
//     template<> struct char_traits<char> {
//       typedef int int_type;
//       static constexpr int_type eof() noexcept
//       { return static_cast<int_type>(-1); }   // <-- type is cpp_name
//     };
//   }
//   template<typename T, typename Tr = synth::char_traits<T>>
//   struct sbuf {
//     typedef typename Tr::int_type int_type;
//     static int_type get_eof() { return Tr::eof(); }
//   };
//   sbuf<char>::get_eof();   // triggers eager-convert of eof
//
// The fix walks the body's full irept tree (operands AND named-sub
// children including `type`) when checking for unresolved cpp_names.

namespace synth
{
template <typename _CharT>
struct char_traits
{
  typedef _CharT char_type;
};

template <>
struct char_traits<char>
{
  typedef char char_type;
  typedef int int_type;
  // The body has `int_type` as the *type* of `static_cast`; that
  // cpp_name was invisible to the previous operands-only walk.
  static constexpr int_type eof() noexcept
  {
    return static_cast<int_type>(-1);
  }
};
} // namespace synth

template <typename T, typename Tr = synth::char_traits<T>>
struct sbuf
{
  typedef typename Tr::int_type int_type;
  // Constexpr inliner substitutes Tr::eof()'s body here; without
  // the fix, the substituted `int_type` cpp_name leaks unresolved.
  static int_type get_eof()
  {
    return Tr::eof();
  }
};

int main()
{
  auto x = sbuf<char>::get_eof();
  (void)x;
  return 0;
}
