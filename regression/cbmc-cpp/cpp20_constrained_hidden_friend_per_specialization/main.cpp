// N5008 [temp.friend]/9: a friend function template with a constraint that
// depends on a template parameter of an enclosing template (`requires
// same_as<Tp, C>') does not declare the same template as a declaration in
// any other scope: closure_base<int> and closure_base<closure_t<bound>> each
// define their own operator| templates.  CBMC gave them one identifier (the
// enclosing argument substituted into the requires-clause was not part of
// it), kept the first specialization's (Tp = int), and `arr | c' took the
// closure | closure overload ("conversion from 'signed int [1l]' to 'struct
// closure_t'").  libc++'s __range_adaptor_closure<_Tp> (views::take) is
// written this way.
extern "C" void __CPROVER_assert(bool, const char *);
template <class T, class U>
concept same_as = __is_same(T, U);
template <class D, class B>
concept derived_from = __is_convertible(D, B);
template <class T>
struct is_lref
{
  static constexpr bool value = false;
};
template <class T>
struct is_lref<T &>
{
  static constexpr bool value = true;
};
template <class T>
concept viewable_range = is_lref<T>::value;
template <class>
struct closure_base;
template <class Fn>
struct closure_t : Fn, closure_base<closure_t<Fn>>
{
};
template <class T>
concept closure = derived_from<T, closure_base<T>>;
template <class Tp>
struct closure_base
{
  template <viewable_range View, closure C>
  requires same_as<Tp, C> friend int operator|(View &&, C)
  {
    return 1;
  }
  template <closure C, closure Other>
  requires same_as<Tp, C> friend int operator|(C, Other)
  {
    return 2;
  }
};
struct other : closure_base<other>
{
};
struct bound
{
};
struct take_fn
{
  auto operator()(int)
  {
    return closure_t<bound>();
  }
} take;
int main()
{
  int arr[1] = {0};
  auto c = take(3);
  __CPROVER_assert((arr | c) == 1, "range | closure");
  __CPROVER_assert((arr | other()) == 1, "other specialization");
  __CPROVER_assert((closure_t<bound>() | other()) == 2, "closure | closure");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
