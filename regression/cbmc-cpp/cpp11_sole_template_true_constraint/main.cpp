// Well-formed counterpart of cpp11_sole_template_false_constraint: the sole
// function template `f`'s non-deduced defaulted template parameter has type
// `enable_if_t<always_true<T>::value, int>` == `enable_if<true,int>::type` ==
// `int`, a valid substitution, so `f` is viable and `f(5)` selects it
// ([temp.deduct]/8 is satisfied).  This guards the fix for the false-constraint
// bug against over-rejection: evaluating the sole candidate's defaulted
// parameter must accept a true constraint.  assertion.2 provides non-vacuity.

extern "C" void __CPROVER_assert(int, const char *);

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
struct always_true
{
  static const bool value = true;
};

template <class T, enable_if_t<always_true<T>::value, int> = 0>
int f(T)
{
  return 7;
}

int main()
{
  __CPROVER_assert(f(5) == 7, "true-constrained sole template is viable");
  __CPROVER_assert(f(5) != 7, "WRONG must FAIL");
  return 0;
}
