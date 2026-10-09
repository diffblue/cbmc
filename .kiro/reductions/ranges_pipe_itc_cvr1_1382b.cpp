template <int __v> struct integral_constant {
  static const int value = __v;
};
namespace std {
template <class _Tp, _Tp...> struct integer_sequence;
template <long... _Ip> using index_sequence = integer_sequence<long, _Ip...>;
template <class _Tp, _Tp _Ep>
using __make_integer_sequence = __make_integer_seq<integer_sequence, _Tp, _Ep>;
template <class _Tp, _Tp _Np>
using make_integer_sequence = __make_integer_sequence<_Tp, _Np>;
template <long _Np>
using make_index_sequence = make_integer_sequence<long, _Np>;
template <class...> struct tuple {};
template <class> struct tuple_size;
template <class... _Tp>
struct tuple_size<tuple<_Tp...>> : integral_constant<sizeof...(_Tp)> {};
template <class _Tp> long tuple_size_v = tuple_size<_Tp>::value;
template <class> struct __perfect_forward_impl;
template <class... _Args>
using __perfect_forward = __perfect_forward_impl<_Args...>;
template <long _NBound, class = make_index_sequence<_NBound>>
struct __bind_back_op;
template <long _NBound, long... _Ip>
struct __bind_back_op<_NBound, index_sequence<_Ip...>>;
template <class, class _BoundArgs>
struct __bind_back_t
    : __perfect_forward<__bind_back_op<tuple_size_v<_BoundArgs>>> {};
template <class _Fn> void __bind_back(_Fn, int) { __bind_back_t<_Fn, tuple<>>; }
int operator0___n;
struct {
  auto operator0() { __bind_back(this, operator0___n); }
} take;
} // namespace std
