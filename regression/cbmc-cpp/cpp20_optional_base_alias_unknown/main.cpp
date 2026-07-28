// Header-free mimic of libc++ std::optional (cvise-reduced from an
// <optional> driver; gates cpp20_map_basic_libcxx, whose conversion
// error is "symbol '__null_state_' is unknown" in the same family).
// The member alias __base for the dependent base class template is not
// resolvable in the instantiated ctor mem-initializer: "symbol
// '__base' is unknown".  clang++ accepts (clang builtins; g++ n/a).

template <bool> struct enable_if;
template <bool _Bp> using enable_if_t = enable_if<_Bp>;
template <int __v> struct integral_constant {
  static const int value = __v;
};
template <class _Tp>
using __add_rvalue_reference_t = __add_rvalue_reference(_Tp);
template <class, class _To> using __copy_cv_t = _To;
template <class, class> using __cond_res = decltype(0);
template <class, class, class, class> struct __common_ref;
template <class _Xp, class _Yp>
using __cv_cond_res = __cond_res<__copy_cv_t<_Xp, _Yp>, __copy_cv_t<_Yp, _Xp>>;
template <class _Ap, class _Bp, class _Xp, class _Yp>
  requires requires { typename __cv_cond_res<_Xp, _Yp>; }
struct __common_ref<_Ap, _Bp, _Xp, _Yp>;
template <bool = integral_constant<__is_trivially_constructible(
              __add_rvalue_reference_t<int>)>::value>
struct __optional_move_assign_base {};
template <class> struct optional : __optional_move_assign_base<> {
  using __base = __optional_move_assign_base;
  optional();
  template <class _Up, enable_if_t> optional(_Up &&);
  template <class _Up, enable_if_t<_Up ::__enable_explicitint>>
  optional(_Up &&) : __base() {}
};
int main()
{
  optional<int> o;
  __CPROVER_assert(true, "conversion clean");
  return 0;
}
