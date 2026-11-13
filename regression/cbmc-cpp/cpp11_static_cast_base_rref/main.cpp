// N5008 [expr.static.cast]/3: an lvalue of type cv1 T1 can be cast to
// "rvalue reference to cv2 T2" if T2 is reference-compatible with T1 --
// including T2 a BASE class of T1 ([dcl.init.ref]/4); the result
// designates the base-class subobject as an xvalue.  This is
// std::_Tuple_impl's move-constructor shape,
// `_Tuple_impl(_Tuple_impl&& __in) : _Base(static_cast<_Base&&>(__in))`,
// behind std::tuple's move construction and therefore std::map's
// piecewise node construction.
//
// Was KNOWNBUG: static_typecast handled `static_cast<T&&>(e)` only for
// e's exact type, so the derived-to-base rvalue-reference cast failed,
// std::tuple's move constructor was silently dropped (system header),
// and the moved-to tuple's reference member read as NULL (std::map's
// operator[] read-back saw a garbage key).
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
template <typename _Tp>
constexpr _Tp &&forward(typename remove_reference<_Tp>::type &__t) noexcept
{
  return static_cast<_Tp &&>(__t);
}
template <typename _Tp>
constexpr _Tp &&forward(typename remove_reference<_Tp>::type &&__t) noexcept
{
  return static_cast<_Tp &&>(__t);
}

template <unsigned long I, typename H>
struct head_base
{
  H _M_head_impl;
  template <typename U>
  head_base(U &&u) : _M_head_impl(forward<U>(u))
  {
  }
  head_base(head_base &&) = default;
};

template <unsigned long I, typename H>
struct tuple_impl : head_base<I, H>
{
  typedef head_base<I, H> _Base;
  template <typename U>
  tuple_impl(U &&u) : _Base(forward<U>(u))
  {
  }
  // the std::_Tuple_impl move-constructor shape
  tuple_impl(tuple_impl &&__in) : _Base(static_cast<_Base &&>(__in))
  {
  }
};

int take(tuple_impl<0, int &&> t)
{
  return t._M_head_impl;
}

int main()
{
  int x = 5;
  tuple_impl<0, int &&> t(static_cast<int &&>(x));
  __CPROVER_assert(
    take(static_cast<tuple_impl<0, int &&> &&>(t)) == 5,
    "reference member survives base-slice move");
  return 0;
}
