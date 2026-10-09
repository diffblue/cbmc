// Regression for [class.conv.ctor]: a user-defined conversion
// sequence may not select an `explicit` constructor.
//
// Before the fix, `user_defined_conversion_sequence`'s template
// fallback (entered when the regular loop finds no non-template
// converting ctor) called `new_temporary` which performs *direct*-
// initialisation overload resolution; that allows explicit
// constructors and finds the explicit `Bad(M)` ctor as a path
// from `int` to `Bad`.  reference_binding then reports `int` as
// bindable to `const Bad&`, making `Bad(M)` and the implicit copy
// ctor `Bad(const Bad&)` both viable for `Bad(0)`, and CBMC reports
//   symbol 'Bad' does not uniquely resolve.
//
// The fix: after `new_temporary`, check whether the selected
// constructor is a template specialisation; reject the conversion
// if it is not, on the grounds that the regular loop has already
// considered every non-template, non-explicit converting ctor and
// found none viable.

struct M
{
  int v;
  M(int x) : v(x)
  {
  }
};

struct Bad
{
  int v;

  // explicit, single-arg, non-template:
  explicit Bad(M m) : v(m.v)
  {
  }

  // template ctors (presence triggers the buggy fallback):
  template <typename Diagnostic, typename... Diagnostics>
  Bad(M m, Diagnostic &&, Diagnostics &&...) : v(m.v)
  {
  }

  template <typename... Diagnostics>
  Bad(M m, int, Diagnostics &&...) : v(m.v)
  {
  }
};

int main()
{
  // Direct ctor call from int — must select the explicit
  // `Bad(M)` ctor unambiguously.  Without the fix, the template
  // fallback in `user_defined_conversion_sequence` accepts the
  // explicit ctor as a hidden user-defined conversion path,
  // which makes the implicit copy ctor `Bad(const Bad&)` *also*
  // appear viable for `Bad(7)`, and CBMC reports
  //   symbol 'Bad' does not uniquely resolve.
  Bad b(7);
  (void)b;
  return 0;
}
