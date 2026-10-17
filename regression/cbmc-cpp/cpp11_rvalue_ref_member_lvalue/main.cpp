// N5008 [expr.ref]/6: a class member access naming a member declared with
// reference type is an LVALUE of the referenced type -- for an
// rvalue-reference member (`int &&m`) just as for an lvalue-reference one.
// So inside a member function, `m` binds to a non-const lvalue reference
// (`int &r = m;`, `return m;` from `int &get()`), and a constructor
// template's forwarded initializer can feed it.  This is the
// std::_Head_base<I, T&&> / std::_Tuple_impl<I, T&&> shape that
// map/tuple's piecewise construction instantiates.
//
// Was KNOWNBUG (2 defects):
// * reference_binding classified EVERY implicit dereference of a
//   non-symbol rvalue-reference as an xvalue, so binding `int&` to the
//   member access failed ("bad reference initializer") and the enclosing
//   member function was dropped;
// * trying a concrete non-viable constructor candidate (the instantiated
//   `_Head_base(const _Head&)` == `_Head_base(int&)` by reference
//   collapsing, [dcl.ref]/6) during overload resolution hard-failed the
//   conversion instead of making the candidate non-viable
//   ([over.best.ics.general]/2), dropping the enclosing constructor.
extern "C" void __CPROVER_assert(int, const char *);

template <typename T>
struct remove_reference
{
  typedef T type;
};
template <typename T>
struct remove_reference<T &>
{
  typedef T type;
};
template <typename T>
struct remove_reference<T &&>
{
  typedef T type;
};

template <typename T>
constexpr T &&forward(typename remove_reference<T>::type &__t) noexcept
{
  return static_cast<T &&>(__t);
}

// [expr.ref]/6 directly: reference member is an lvalue inside members
struct B
{
  int &&m;
  B(int &&v) : m(static_cast<int &&>(v))
  {
  }
  int &get()
  {
    return m; // lvalue of type int
  }
  int get_val()
  {
    int &r = m; // binds a non-const lvalue reference
    return r;
  }
};

// the _Head_base/_Tuple_impl shape: base initializer forwards into a
// reference member of the (private) base
template <unsigned long _Idx, typename _Head>
struct head_base
{
  template <typename _UHead>
  constexpr head_base(_UHead &&__h) : _M_head_impl(forward<_UHead>(__h))
  {
  }
  _Head _M_head_impl;
};

template <unsigned long _Idx, typename _Head>
struct tuple_impl : private head_base<_Idx, _Head>
{
  typedef head_base<_Idx, _Head> _Base;

  static constexpr _Head &_M_head(tuple_impl &__t) noexcept
  {
    return __t._M_head_impl;
  }

  template <typename _UHead>
  explicit constexpr tuple_impl(_UHead &&__head)
    : _Base(forward<_UHead>(__head))
  {
  }
};

int main()
{
  int x = 42;
  B b(static_cast<int &&>(x));
  __CPROVER_assert(b.get() == 42, "reference member reads through");
  b.get() = 7;
  __CPROVER_assert(x == 7, "reference member aliases x");
  __CPROVER_assert(b.get_val() == 7, "local lvalue-ref binding to member");

  int y = 5;
  tuple_impl<0, int &&> t(static_cast<int &&>(y));
  __CPROVER_assert(tuple_impl<0, int &&>::_M_head(t) == 5, "tuple head bound");
  tuple_impl<0, int &&>::_M_head(t) = 9;
  __CPROVER_assert(y == 9, "tuple head aliases y");
  return 0;
}
