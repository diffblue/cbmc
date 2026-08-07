template <int __v> struct integral_constant {
  static const bool value = __v;
};
template <bool _Val> using _BoolConstant = integral_constant<_Val>;
template <class _Tp, class _Up>
using _IsSame = _BoolConstant<__is_same(_Tp, _Up)>;
template <class _Tp> struct enable_if {
  typedef _Tp type;
};
template <bool, class _Tp = void> using __enable_if_t = enable_if<_Tp>::type;
template <class _From, class _To>
constexpr bool is_convertible_v = __is_convertible(_From, _To);
template <class _Dp, class _Bp>
concept derived_from = is_convertible_v<_Dp *, _Bp *>;
template <template <class> class, class>
integral_constant<false> __sfinae_test_impl();
template <template <class> class _Templ, class... _Args>
using _IsValidExpansion = decltype(__sfinae_test_impl<_Templ, _Args...>());
template <class _Tp>
using __test_for_primary_template =
    __enable_if_t<_IsSame<_Tp, typename _Tp::__primary_template>::value>;
template <class _Tp>
using __is_primary_template =
    _IsValidExpansion<__test_for_primary_template, _Tp>;
template <class> using iter_difference_t = long;
template <int> struct _OrImpl {
  template <class, class _First, class... _Rest>
  using _Result = _OrImpl<sizeof...(_Rest)>::template _Result<_First>;
};
template <> struct _OrImpl<false> {
  template <class _Res> using _Result = _Res;
};
template <class... _Args>
using _Or = _OrImpl<sizeof...(_Args)>::template _Result<_Args...>;
struct forward_iterator_tag;
struct __iter_concept_random_fallback {
  template <class _Iter>
  using _Apply =
      __enable_if_t<__is_primary_template<_Iter>::value, forward_iterator_tag>;
};
struct __iter_concept_cache {
  using type = _Or<int, __iter_concept_random_fallback>;
};
template <class _Iter>
using _ITER_CONCEPT = __iter_concept_cache::type::_Apply<_Iter>;
template <class _Sp, class>
concept sized_sentinel_for = requires(_Sp __s) { __s; };
template <class _Ip>
concept forward_iterator =
    derived_from<_ITER_CONCEPT<_Ip>, forward_iterator_tag>;
using ::uintmax_t __attribute__((__using_if_exists__));
struct {
  template <class _Tp, int _Np> auto operator()(_Tp (&__t)[_Np]) { return __t; }
  template <class _Tp> auto operator()(_Tp);
} end;
template <class _Tp>
concept forward_range = forward_iterator<_Tp>;
struct {
  template <class _Ip, sized_sentinel_for<_Ip> _Sp>
  iter_difference_t<_Ip> operator()(_Ip, _Sp __last) {
    return __last - _Ip();
  }
} Trans_NS_ranges_distance, distance = Trans_NS_ranges_distance;
struct identity {};
template <class, class _Iter, class _Sent, class _Type, class _Proj,
          class _Comp>
void __lower_bound(_Iter __first, _Sent __last, _Type, _Comp, _Proj) {
  distance(__first, __last);
}
struct {
  template <forward_range _Range, class _Type, class _Proj = identity>
  _Range operator()(_Range &&__r, _Type __value, _Proj __proj = {}) {
    auto __comp_lhs_rhs_swapped = [] {};
    auto __trans_tmp_1 = __r, __trans_tmp_2 = end(__r);
    __lower_bound<int>(__trans_tmp_1, __trans_tmp_2, __value,
                       __comp_lhs_rhs_swapped, __proj);
  }
} upper_bound;
unsigned __entries[]{0};
long __estimated_width___i = upper_bound(__entries, 5) - __entries;
