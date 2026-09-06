// N5008 [temp.local]/1 + [temp.friend]/1: inside a class template, a
// hidden friend's REQUIRES-CLAUSE may name the enclosing template's
// own parameter.  This is libc++'s __range_adaptor_closure
//   template <class _Tp> struct __range_adaptor_closure {
//     template <viewable_range _View, _RangeAdaptorClosure _Closure>
//       requires same_as<_Tp, remove_cvref_t<_Closure>> && ...
//     friend constexpr decltype(auto) operator|(_View&&, _Closure&&);
//   };
// (the CRTP base that makes `arr | views::take(3)` work).  CBMC hoists
// the friend to namespace scope and fails to resolve `Tp` in the
// requires-clause ("symbol 'Tp' is unknown"), drops the candidate, and
// the pipe expression falls back to arithmetic conversion.  Sibling of
// the fixed nested-class default-argument case
// (cpp20_member_class_template_own_param_friend): this one is a
// TOP-LEVEL class template and the parameter appears in the
// CONSTRAINT, not a default argument.  One of the two remaining
// blockers of cpp20_ranges_basic_libcxx.
extern "C" void __CPROVER_assert(bool, const char *);
template <class T, class U> struct is_same_
{
  static const bool value = false;
};
template <class T> struct is_same_<T, T>
{
  static const bool value = true;
};
template <class T> struct remove_cvref_
{
  using type = T;
};
template <class T> struct remove_cvref_<T &>
{
  using type = T;
};
template <class T> struct remove_cvref_<T &&>
{
  using type = T;
};
template <class T, class U>
concept same_as_ = is_same_<T, typename remove_cvref_<U>::type>::value;
template <class Tp> struct closure_base
{
  template <class View, class Closure>
    requires same_as_<Tp, Closure>
  friend decltype(auto) operator|(View &&v, Closure &&c)
  {
    return c(v);
  }
};
struct times2 : closure_base<times2>
{
  int operator()(int x) const
  {
    return 2 * x;
  }
};
int main()
{
  times2 t;
  int r = 21 | t;
  __CPROVER_assert(r == 42, "pipe through CRTP closure base");
  return 0;
}
