// libc++'s tuple_size shape (three interacting front-end defects, all
// required for `tuple_size<Tup<int,int>>::value == 2`):
//
// 1. N5008 [temp.deduct.type]/8: the alias-pattern partial
//    specialization `tuple_size<__enable_if_tuple_size_imp<const _Tp,
//    ...>>` must FAIL deduction against a non-const argument.  The
//    guesser stripped the const and bound _Tp, and re-type-checking
//    the pattern then evaluated `sizeof(tuple_size<_Tp>)` -- re-
//    entering the disambiguation in progress, exponentially (~500k
//    candidate iterations, minutes of churn before a depth error).
// 2. N5008 [temp.alias]/2: a cv-qualified alias argument (`const _Tp`)
//    must be substituted into the alias body; it was skipped (only
//    plain names were), leaving the alias's own parameter name to
//    collide with the specialization's.
// 3. N5008 [temp.variadic]/5: expanding `Tup<_Tp...>` in a partial-
//    specialization pattern must substitute the pack's i-th ELEMENT;
//    the emitted argument kept the name `_Tp`, which later resolved
//    against the PRIMARY template's identically-named parameter (bound
//    to the whole argument), so `tuple_size<Tup<_Tp...>>` re-type-
//    checked as `tuple_size<Tup<Tup<int,int>, Tup<int,int>>>` and the
//    specialization never matched.
extern "C" void __CPROVER_assert(bool, const char *);
typedef unsigned long size_t;
template <class T, T v>
struct integral_constant
{
  static const T value = v;
};
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
using __enable_if_t = typename enable_if<B, T>::type;
template <class _Tp>
struct is_volatile
{
  static const bool value = false;
};
template <class... _Tp>
struct Tup
{
};

template <class _Tp>
struct tuple_size;
template <class _Tp, class...>
using __enable_if_tuple_size_imp = _Tp;
template <class _Tp>
struct tuple_size<__enable_if_tuple_size_imp<
  const _Tp,
  __enable_if_t<!is_volatile<_Tp>::value>,
  integral_constant<size_t, sizeof(tuple_size<_Tp>)>>>
  : public integral_constant<size_t, tuple_size<_Tp>::value>
{
};
template <class... _Tp>
struct tuple_size<Tup<_Tp...>>
  : public integral_constant<size_t, sizeof...(_Tp)>
{
};

int main()
{
  unsigned long v = tuple_size<Tup<int, int>>::value;
  __CPROVER_assert(v == 2, "ts");
  return 0;
}
