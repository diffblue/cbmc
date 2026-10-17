# 1 "/usr/lib/llvm-18/lib/clang/18/include/__stddef_offsetof.h"
namespace std
{
template <class _Tp>
constexpr bool is_lvalue_reference_v = __is_lvalue_reference(_Tp);
template <class _From, class _To>
constexpr bool is_convertible_v = __is_convertible(_From, _To);
template <class _From, class>
concept convertible_to = requires
{
  _From();
};
template <class _Dp, class _Bp>
concept derived_from = is_convertible_v<_Dp, _Bp>;
template <class _Tp, _Tp>
struct integer_sequence;
template <class...>
struct __perfect_forward_impl;
template <class _Op, long... _Idx, class... _BoundArgs>
struct __perfect_forward_impl<
  _Op,
  integer_sequence<unsigned long, _Idx...>,
  _BoundArgs...>
{
  template <class... _Args>
  auto operator()(_Args... __args) -> decltype(_Op()(_Idx..., __args...));
};
template <class _Op, class... _Args>
using __perfect_forward =
  __perfect_forward_impl<_Op, integer_sequence<unsigned long, 0>>;
namespace ranges
{
template <class _Tp>
concept viewable_range = is_lvalue_reference_v<_Tp>;
}
template <class>
struct __range_adaptor_closure;
template <class _Fn>
struct __range_adaptor_closure_t : _Fn, __range_adaptor_closure<_Fn>
{
};
template <class _Tp>
concept _RangeAdaptorClosure = derived_from<_Tp, _Tp>;
template <class>
struct __range_adaptor_closure
{
  template <ranges::viewable_range _View, _RangeAdaptorClosure _Closure>
  friend auto operator|(_View &&__view, _Closure __closure)
  {
    return __closure(__view);
  }
};
template <class _Fn>
struct __bind_back_t : __perfect_forward<_Fn, int>
{
};
template <class _Fn>
auto __bind_back(_Fn...) -> decltype(__bind_back_t<_Fn>());
namespace ranges
{
template <class _View>
struct take_view
{
  _View __base_;
  _View __count_;
  int *begin();
  int *end();
};
struct Trans_NS___take___fn
{
  template <class _Range, convertible_to<_Range> _Np>
  auto operator()(_Range, _Np __n) -> decltype(take_view(__n));
  template <class _Np>
  auto operator()(_Np)
  {
    return __range_adaptor_closure_t(__bind_back(*this, _Np()));
  }
} take;
} // namespace ranges
namespace views = ranges;
} // namespace std
# 4 ""
int main()
{
  int arr;
  for(auto x : arr | std::views::take(3))
    __CPROVER_assert;
}
