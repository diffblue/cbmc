template <class _Tp> struct enable_if {
  typedef _Tp type;
};
# 1 "/usr/lib/llvm-18/lib/clang/18/include/__stddef_offsetof.h"
namespace std {
template <class _Tp>
constexpr bool is_lvalue_reference_v = __is_lvalue_reference(_Tp);
template <class _From, class _To>
constexpr bool is_convertible_v = __is_convertible(_From, _To);
template <class _From, class>
concept convertible_to = requires { _From(); };
template <bool, class _If, class> using __conditional_t = _If;
template <class _Dp, class _Bp>
concept derived_from = is_convertible_v<_Dp, _Bp>;
template <class _Fp, class... _Args>
decltype(_Fp()(_Args()...)) __invoke(_Fp, _Args...);
template <class, class _Fp, class... _Args> struct __invokable_r {
  template <class _XFp, class... _XArgs>
  static decltype(__invoke(_XFp(), _XArgs()...)) __try_call(int);
  using _Result = decltype(__try_call<_Fp, _Args...>(0));
};
template <class _Fp, class... _Args>
struct __invoke_of
    : enable_if<typename __invokable_r<void, _Fp, _Args...>::_Result> {};
template <class _Fn, class... _Args>
using invoke_result_t = __invoke_of<_Fn, _Args...>::type;
template <class _Fn, class... _Args>
invoke_result_t<_Fn, _Args...> invoke(_Fn, _Args...);
template <class _Ip>
concept input_or_output_iterator = requires(_Ip __i) { __i; };
namespace ranges {
template <class> using iterator_t = decltype(0);
auto end = int{};
} // namespace ranges
template <class _Tp, _Tp> struct integer_sequence;
template <long... _Ip>
using index_sequence = integer_sequence<unsigned long, _Ip...>;
template <class _Tp, _Tp _Ep>
using __make_integer_sequence = __make_integer_seq<integer_sequence, _Tp, _Ep>;
template <class _Tp, _Tp _Np>
using make_integer_sequence = __make_integer_sequence<_Tp, _Np>;
template <long _Np>
using make_index_sequence = make_integer_sequence<unsigned long, _Np>;
template <class... _Tp>
using index_sequence_for = make_index_sequence<sizeof...(_Tp)>;
template <bool _Const, class _Tp>
using __maybe_const = __conditional_t<_Const, _Tp, _Tp>;
template <class...> struct __perfect_forward_impl;
template <class _Op, long... _Idx, class... _BoundArgs>
struct __perfect_forward_impl<_Op, index_sequence<_Idx...>, _BoundArgs...> {
  template <class... _Args>
  auto operator()(_Args... __args) -> decltype(_Op()(_Idx..., __args...));
};
template <class _Op, class... _Args>
using __perfect_forward =
    __perfect_forward_impl<_Op, index_sequence_for<_Args...>>;
namespace ranges {
template <class> constexpr bool enable_view = requires { nullptr; };
template <class _Tp>
concept view = enable_view<_Tp>;
template <class _Tp>
concept viewable_range = is_lvalue_reference_v<_Tp>;
} // namespace ranges
template <class> struct __range_adaptor_closure;
template <class _Fn>
struct __range_adaptor_closure_t : _Fn, __range_adaptor_closure<_Fn> {};
template <class _Tp>
concept _RangeAdaptorClosure = derived_from<_Tp, _Tp>;
template <class> struct __range_adaptor_closure {
  template <ranges::viewable_range _View, _RangeAdaptorClosure _Closure>
  friend auto operator|(_View &&__view, _Closure __closure) {
    return invoke(__closure, __view);
  }
};
template <class _Fn> struct __bind_back_t : __perfect_forward<_Fn, int> {};
template <class _Fn> auto __bind_back(_Fn...) -> decltype(__bind_back_t<_Fn>());
template <input_or_output_iterator _Iter> struct counted_iterator {
  counted_iterator(_Iter, _Iter);
  auto operator*() { return __current_; }
  void operator++();
  _Iter __current_;
};
namespace ranges {
template <view _View> struct take_view {
  _View __base_;
  _View __count_;
  template <bool> class __sentinel;
  auto begin() { return counted_iterator(__base_, __count_); }
  auto end() { return __sentinel<true>{ranges::end}; }
};
template <view _View>
template <bool _Const>
struct take_view<_View>::__sentinel {
  using _Base = __maybe_const<_Const, _View>;
  template <bool _OtherConst>
  using _Iter = counted_iterator<iterator_t<__maybe_const<_OtherConst, _View>>>;
  __sentinel(_Base);
  friend bool operator==(_Iter<_Const>, __sentinel);
};
struct Trans_NS___take___fn {
  template <class _Range, convertible_to<_Range> _Np>
  auto operator()(_Range, _Np __n) -> decltype(take_view(__n));
  template <class _Np> auto operator()(_Np) {
    return __range_adaptor_closure_t(__bind_back(*this, _Np()));
  }
} take;
} // namespace ranges
namespace views = ranges;
} // namespace std
# 4 ""
int main() {
  int arr;
  for (auto x : arr | std::views::take(3))
    __CPROVER_assert;
}
