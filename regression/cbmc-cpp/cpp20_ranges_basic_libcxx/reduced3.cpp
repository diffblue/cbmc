void __CPROVER_assert(bool, char *);
#pragma clang attribute _LibcxxExplicitABIAnnotations.push
namespace std
{
template <class _Tp, _Tp __v>
struct integral_constant
{
  static const _Tp value = __v;
};
template <bool _Val>
using _BoolConstant = integral_constant<bool, _Val>;
template <class _Tp>
constexpr bool is_class_v = __is_class(_Tp);
template <class _Tp>
_Tp __declval(int);
template <class _Tp>
decltype(__declval<_Tp>(0)) declval();
template <class _From, class>
concept convertible_to = requires
{
  _From();
};
template <class _Tp, class _Up>
using _IsSame = _BoolConstant<__is_same(_Tp, _Up)>;
template <class _Tp, class _Up>
concept __same_as_impl = _IsSame<_Tp, _Up>::value;
template <class _Tp, class _Up>
concept same_as = __same_as_impl<_Up, _Tp>;
struct _IfImpl
{
  template <class, class _ElseRes>
  using _Select = _ElseRes;
};
template <bool, class _IfRes, class _ElseRes>
using _If = _IfImpl::_Select<_IfRes, _ElseRes>;
template <int _Bp, class _ElseRes>
struct conditional
{
  using type = _If<_Bp, int, _ElseRes>;
};
template <bool _Bp, class, class _ElseRes>
using conditional_t = conditional<_Bp, _ElseRes>::type;
template <class...>
using __void_t = void;
template <class _Tp>
constexpr bool is_lvalue_reference_v = __is_lvalue_reference(_Tp);
inline namespace
{
template <class _Rhs>
concept assignable_from = requires(_Rhs __rhs)
{
  __rhs;
};
template <class, class... _Args>
struct __invoke_result_impl
{
  using type = decltype(__builtin_invoke(declval<_Args>()...));
};
template <class... _Args>
using __invoke_result = __invoke_result_impl<void, _Args...>;
template <class... _Args>
using __invoke_result_t = __invoke_result<_Args...>::type;
template <class _Fn, class... _Args>
using invoke_result_t = __invoke_result_t<_Fn, _Args...>;
template <class _Fn, class... _Args>
invoke_result_t<_Fn, _Args...> invoke(_Fn, _Args...);
template <class _Fn>
concept invocable = requires(_Fn __fn)
{
  __fn;
};
template <class>
concept __primary_template = requires
{
  typename __void_t<>;
};
template <class>
struct iterator_traits
{
  typedef decltype(static_cast<int *>(nullptr) - static_cast<int *>(nullptr))
    difference_type;
};
template <class _Ip>
using iter_difference_t = conditional_t<
  __primary_template<iterator_traits<_Ip>>,
  int,
  iterator_traits<_Ip>>::difference_type;
template <decltype(sizeof(int)), class>
struct tuple_element;
template <class...>
struct tuple
{
};
template <decltype(sizeof(int)) _Ip, class... _Tp>
struct tuple_element<_Ip, tuple<_Tp...>>
{
  using type = __type_pack_element<_Ip, _Tp...>;
};
template <decltype(sizeof(int)) _Ip, class... _Tp>
tuple_element<_Ip, tuple<_Tp...>>::type get(tuple<_Tp...>);
template <class _In>
concept __indirectly_readable_impl = requires(_In __i)
{
  __i;
};
template <class _Sp>
concept sized_sentinel_for = requires(_Sp __s)
{
  __s;
};
namespace ranges
{
template <class _Tp>
concept __member_begin = requires(_Tp __t)
{
  __t;
};
struct Trans_NS___begin___fn
{
  template <class _Tp>
  auto operator()(_Tp __t)
  {
    return __t.begin();
  }
} begin;
} // namespace ranges
template <class>
struct tuple_size;
template <class... _Tp>
struct tuple_size<tuple<_Tp...>>
  : integral_constant<decltype(sizeof(int)), sizeof...(_Tp)>
{
};
template <class _Tp>
constexpr decltype(sizeof(int)) tuple_size_v = tuple_size<_Tp>::value;
template <template <class> class _BaseType, class _Tp, _Tp _SequenceSize>
using __make_integer_sequence_impl =
  __make_integer_seq<_BaseType, _Tp, _SequenceSize>;
template <class, int...>
struct integer_sequence;
template <decltype(sizeof(int))... _Ip>
using index_sequence = integer_sequence<decltype(sizeof(int)), _Ip...>;
template <class _Tp, _Tp _Ep>
using make_integer_sequence =
  __make_integer_sequence_impl<integer_sequence, _Tp, _Ep>;
template <decltype(sizeof(int)) _Np>
using make_index_sequence = make_integer_sequence<decltype(sizeof(int)), _Np>;
template <class... _Tp>
using index_sequence_for = make_index_sequence<sizeof...(_Tp)>;
template <class...>
struct __perfect_forward_impl;
template <class _Op, decltype(sizeof(int))... _Idx, class... _BoundArgs>
struct __perfect_forward_impl<_Op, index_sequence<_Idx...>, _BoundArgs...>
{
  tuple<_BoundArgs...> __bound_args_;
  template <class _Args>
  __perfect_forward_impl(_Args);
  template <class... _Args>
  auto operator()(_Args... __args)
    -> decltype(_Op()(get<_Idx>(__bound_args_)..., __args...));
};
template <class _Op, class... _Args>
using __perfect_forward =
  __perfect_forward_impl<_Op, index_sequence_for<_Args...>, _Args...>;
namespace
{
template <class _Yp>
void __is_derived_from_view_interface(_Yp);
template <class _Tp>
constexpr bool enable_view = requires
{
  __is_derived_from_view_interface<_Tp>(nullptr);
};
template <class _Tp>
concept range = requires(_Tp __t)
{
  __t;
};
template <range _Rp>
using range_difference_t = iter_difference_t<_Rp>;
template <class _Tp>
concept view = enable_view<_Tp>;
template <class _Tp>
concept viewable_range = is_lvalue_reference_v<_Tp>;
;
template <class _Fn>
struct __pipeable : _Fn
{
};
template <class>
concept _RangeAdaptorClosure = requires
{
  nullptr;
};
template <range _Range, _RangeAdaptorClosure _Closure>
auto operator|(_Range __range, _Closure __closure)
{
  return invoke(__closure, __range);
}
template <range _Range>
struct ref_view
{
  template <class _Tp>
  ref_view(_Tp);
  _Range begin();
};
template <class _Range>
ref_view(_Range) -> ref_view<_Range>;
} // namespace
namespace ranges::views
{
struct __fn
{
  template <class _Tp>
  auto operator()(_Tp &&__t)
  {
    return ref_view{__t};
  }
};
namespace
{
auto all = __fn{};
}
template <viewable_range _Range>
using all_t = decltype(all(declval<_Range>()));
} // namespace ranges::views
template <decltype(sizeof(int)) _NBound, class = make_index_sequence<_NBound>>
struct __bind_back_op;
template <decltype(sizeof(int)) _NBound, decltype(sizeof(int))... _Ip>
struct __bind_back_op<_NBound, index_sequence<_Ip...>>
{
  template <class _Fn, class _BoundArgs, class... _Args>
  auto operator()(_Fn __f, _BoundArgs __bound_args, _Args... __args)
    -> decltype(invoke(__f, __args..., get<_Ip>(__bound_args)...));
};
template <class _Fn>
struct __bind_back_t
  : __perfect_forward<__bind_back_op<tuple_size_v<tuple<int>>>, _Fn, tuple<int>>
{
};
tuple<> __trans_tmp_1;
template <class _Fn>
auto __bind_back(_Fn, ...) -> decltype(__bind_back_t<_Fn>(__trans_tmp_1));
namespace ranges
{
template <view _View>
struct take_view
{
  _View __base_;
  _View take_view;
  auto begin()
  {
    return ranges::begin(__base_);
  }
  auto end()
  {
    return ranges::begin(__base_);
  }
};
template <class _Range>
take_view(_Range &&, range_difference_t<_Range>)
  -> take_view<views::all_t<_Range>>;
namespace views
{
struct Trans_NS___take___fn
{
  template <class _Range, convertible_to<_Range> _Np>
  auto operator()(_Range __range, _Np __n) -> decltype(take_view(__range, __n));
  template <class _Np>
  constexpr auto operator()(_Np __n)
  {
    return __pipeable(__bind_back(*this));
  }
};
namespace
{
auto take = Trans_NS___take___fn{};
}
} // namespace views
} // namespace ranges
namespace views = ranges::views;
} // namespace
} // namespace std
#pragma clang attribute _LibcxxExplicitABIAnnotations.pop
int main()
{
  int arr[]{1, 2, 3, 4, 5};
  int sum;
  for(auto x : arr | std::views::take(3))
    __CPROVER_assert(sum == 6, "ranges take");
}
