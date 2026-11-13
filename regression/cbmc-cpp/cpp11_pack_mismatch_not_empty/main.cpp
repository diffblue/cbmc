// N5008 [temp.deduct.type]/8: when P and A have incompatible forms --
// P = `tuple<_Elements...>&` against A = `int*` -- the ENTIRE deduction
// fails and the candidate is removed from the overload set.  The pack is
// not "deduced empty".  This is libstdc++'s constrained tuple-swap
// overload `enable_if<__and_<__is_swappable<_Elements>...>>::type
// swap(tuple<_Elements...>&, tuple<_Elements...>&)` visible next to
// generic `std::swap` when a class member `swap` does the
// `using std::swap; swap(_M_pkey, ...)` two-step (the _Node_handle shape).
//
// Was KNOWNBUG: the failed pack was resurrected as an EMPTY pack, the
// enable_if constraint was substituted with the zero-length-pack sentinel
// (void), and `swap<void>`'s DEFINITION was instantiated collaterally --
// its `void __tmp` local aborted the enclosing conversion chain
// (map's _M_emplace_hint_unique left bodyless).
extern "C" void __CPROVER_assert(int, const char *);

struct true_type
{
  static const bool value = true;
};
struct false_type
{
  static const bool value = false;
};
template <bool, typename T = void>
struct enable_if
{
};
template <typename T>
struct enable_if<true, T>
{
  typedef T type;
};
template <typename...>
struct __and_;
template <>
struct __and_<> : true_type
{
};
template <typename B1>
struct __and_<B1> : B1
{
};
template <typename B1, typename... Bn>
struct __and_<B1, Bn...>
{
  static const bool value = B1::value && __and_<Bn...>::value;
};

template <typename _Tp, typename _Up = _Tp &&>
_Up __declval(int);
template <typename _Tp>
_Tp __declval(long);
template <typename _Tp>
auto declval() noexcept -> decltype(__declval<_Tp>(0));

namespace stdx
{
// generic swap (bits/move.h): definition with a local T __tmp
template <typename _Tp>
void swap(_Tp &__a, _Tp &__b)
{
  _Tp __tmp = __a;
  __a = __b;
  __b = __tmp;
}

// __is_swappable probe
struct __do_is_swappable_impl
{
  template <
    typename _Tp,
    typename = decltype(swap(declval<_Tp &>(), declval<_Tp &>()))>
  static true_type __test(int);
  template <typename>
  static false_type __test(...);
};
template <typename _Tp>
struct __is_swappable_impl : __do_is_swappable_impl
{
  typedef decltype(__test<_Tp>(0)) type;
};
template <typename _Tp>
struct __is_swappable : __is_swappable_impl<_Tp>::type
{
};

template <typename... _Elements>
struct tuple
{
};

// the variadic constrained tuple-swap overload
template <typename... _Elements>
typename enable_if<__and_<__is_swappable<_Elements>...>::value>::type
swap(tuple<_Elements...> &__x, tuple<_Elements...> &__y);
} // namespace stdx

// _Node_handle-like class whose member swap calls unqualified swap on a
// NON-tuple member via the using-declaration two-step
struct handle
{
  int *_M_pkey = nullptr;
  void swap(handle &__nh)
  {
    using stdx::swap;
    swap(_M_pkey, __nh._M_pkey);
  }
};

int main()
{
  handle a, b;
  int x = 1, y = 2;
  a._M_pkey = &x;
  b._M_pkey = &y;
  a.swap(b);
  __CPROVER_assert(a._M_pkey == &y, "swapped a");
  __CPROVER_assert(b._M_pkey == &x, "swapped b");
  return 0;
}
