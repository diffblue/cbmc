// N5008 [temp.deduct]/8, [temp.deduct.general]: if substituting the deduced
// template arguments into the function template's declaration (including the
// types of its template parameters and their default template arguments) would
// be ill-formed, deduction fails and the specialization is removed from the
// overload set.  Here the sole candidate `f`'s trailing, non-deduced template
// parameter has type `enable_if_t<always_false<T>::value, int>`, i.e.
// `enable_if<false, int>::type`, which does not exist -- a substitution
// failure.  The candidate must therefore be removed, leaving no viable function
// for `f(5)`, so the program is ill-formed and must be rejected.  g++ and
// clang++ reject it ("no matching function").
//
// CBMC used to evaluate the constraint carried by a non-deduced defaulted
// template parameter only when a *second* candidate forced disambiguation; a
// sole candidate was deduced from the call argument alone and its defaulted
// parameter's substitution was never checked, so the ill-formed program was
// wrongly accepted (VERIFICATION SUCCESSFUL).
//
// KNOWN BUG.  Flip to CORE once the sole-candidate substitution is checked.
// The well-formed, true-constraint counterpart is exercised (and its members
// verified non-vacuously) by cpp11_sole_template_true_constraint.

template <bool B, class T = void>
struct enable_if
{
};
template <class T>
struct enable_if<true, T>
{
  typedef T type;
};
template <bool B, class T = void>
using enable_if_t = typename enable_if<B, T>::type;

template <class T>
struct always_false
{
  static const bool value = false;
};

template <class T, enable_if_t<always_false<T>::value, int> = 0>
int f(T)
{
  return 1;
}

int main()
{
  // No viable f: the only candidate is removed by [temp.deduct]/8.
  return f(5);
}
