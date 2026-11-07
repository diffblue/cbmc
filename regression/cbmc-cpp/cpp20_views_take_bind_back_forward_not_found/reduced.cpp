extern "C" void __CPROVER_assert(bool, const char *);
// cvise reduction of libc++ 18's views::take(3) (take_view.h:348,
// __bind_back / __perfect_forward / tuple); clang builtins
// __make_integer_seq and __type_pack_element
template <int __v>
struct integral_constant
{
  static const int value = __v;
};
struct __apply_cv_impl
{
  template <class _Up>
  using __apply = _Up;
};
template <class, class _Up>
using __apply_cv_t = __apply_cv_impl::__apply<_Up>;
template <class... _Args>
void invoke();
template <unsigned long...>
struct __tuple_indices
{
};
template <class _IdxType, _IdxType... _Values>
struct __integer_sequence
{
  template <long>
  using __to_tuple_indices = __tuple_indices<_Values...>;
};
template <long _Ep, long _Sp>
using __make_indices_imp =
  __make_integer_seq<__integer_sequence, long, _Ep - _Sp>::
    template __to_tuple_indices<_Sp>;
template <class _Tp, _Tp...>
struct integer_sequence;
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
template <class...>
class tuple;
template <int _Ep, long _Sp = 0>
struct __make_tuple_indices
{
  typedef __make_indices_imp<_Ep, _Sp> type;
};
template <class...>
struct __tuple_types
{
};
template <class>
struct tuple_size;
template <class... _Tp>
struct tuple_size<tuple<_Tp...>> : integral_constant<sizeof...(_Tp)>
{
};
template <class, class>
struct __make_tuple_types_flat;
template <template <class...> class _Tuple, class... _Types, long... _Idx>
struct __make_tuple_types_flat<_Tuple<_Types...>, __tuple_indices<_Idx...>>
{
  template <class _Tp>
  using __apply_quals =
    __tuple_types<__apply_cv_t<_Tp, __type_pack_element<_Idx, _Types...>>...>;
};
template <class _Tp, long _Ep = tuple_size<_Tp>::value, long _Sp = 0>
struct __make_tuple_types
{
  using type = __make_tuple_types_flat<
    _Tp,
    typename __make_tuple_indices<_Ep, _Sp>::type>::template __apply_quals<_Tp>;
};
template <class _Hp>
struct __tuple_leaf
{
  _Hp __value_;
};
template <class...>
struct __tuple_impl;
template <long... _Indx, class... _Tp>
struct __tuple_impl<__tuple_indices<_Indx...>, _Tp...> : __tuple_leaf<_Tp>...
{
  template <unsigned long... _Uf, class... _Tf, class... _Up>
  __tuple_impl(
    __tuple_indices<_Uf...>,
    __tuple_types<_Tf...>,
    __tuple_indices<>,
    __tuple_types<>,
    _Up... __u)
    : __tuple_leaf<_Tf>(__u)...
  {
  }
};
template <class... _Tp>
struct tuple
{
  __tuple_impl<typename __make_tuple_indices<sizeof...(_Tp)>::type, _Tp...>
    __base_;
  template <class... _Up>
  tuple(_Up... __u)
    : __base_(
        typename __make_tuple_indices<sizeof...(_Up)>::type(),
        typename __make_tuple_types<tuple>::type(),
        typename __make_tuple_indices<sizeof...(_Tp), sizeof...(_Up)>::type(),
        typename __make_tuple_types<tuple, sizeof...(_Tp), sizeof...(_Up)>::
          type(),
        __u...)
  {
  }
};
tuple<> forward_as_tuple(int);
template <class _Tp>
constexpr long tuple_size_v = tuple_size<_Tp>::value;
template <class...>
struct __perfect_forward_impl;
template <class _Op, long... _Idx, class... _BoundArgs>
struct __perfect_forward_impl<_Op, index_sequence<_Idx...>, _BoundArgs...>
{
  tuple<_BoundArgs...> __bound_args_;
  template <class... _Args>
  __perfect_forward_impl(_Args... __bound_args) : __bound_args_(__bound_args...)
  {
  }
};
template <class _Op, class... _Args>
using __perfect_forward =
  __perfect_forward_impl<_Op, index_sequence_for<>, _Args...>;
template <long>
struct __bind_back_op;
template <class _Fn, class _BoundArgs>
struct __bind_back_t
  : __perfect_forward<__bind_back_op<tuple_size_v<_BoundArgs>>, _Fn, _BoundArgs>
{
  using __perfect_forward<
    __bind_back_op<tuple_size_v<_BoundArgs>>,
    _Fn,
    _BoundArgs>::__perfect_forward;
};
int __bind_back___f;
template <class... _Args>
auto __bind_back(_Args... __args)
  -> decltype(__bind_back_t<int *, tuple<_Args...>>(
    forward_as_tuple(__args...)))
{
  return __bind_back_t<int *, tuple<_Args...>>(&__bind_back___f, 0);
}
struct
{
  template <class _Np>
  auto operator()(_Np __n)
  {
    __bind_back(__n);
  }
} Trans_NS_Trans_Anon_NS2_take;
int main()
{
  Trans_NS_Trans_Anon_NS2_take(3);
  int reached = 1;
  __CPROVER_assert(reached == 1, "the closure converts");
  __CPROVER_assert(reached == 2, "WRONG (must FAIL)");
}
