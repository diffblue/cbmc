// Distilled from libc++ <functional>'s __bind_back_t (the ranges pipe
// adaptor): a class template INHERITING CONSTRUCTORS ([class.inhctor.init])
// from a partial-specialization-selected base whose arguments involve a
// variable template (tuple_size_v) and __make_integer_seq.  The front
// end converts this, but symex CRASHES on an invariant:
//   goto_symex.cpp:80 symex_assign: lhs.type() == rhs.type()
// i.e. the synthesized inherited/default constructor assigns with
// mismatched types (front-end wrong-code surfacing as a back-end
// invariant).  clang++ accepts and runs this clean.
extern "C" void __CPROVER_assert(bool, const char *);
template <int __v> struct integral_constant {
  static const int value = __v;
};
template <class _Tp, _Tp...> struct integer_sequence {};
template <long... _Ip> using index_sequence = integer_sequence<long, _Ip...>;
template <class _Tp, _Tp _Ep>
using __make_integer_sequence = __make_integer_seq<integer_sequence, _Tp, _Ep>;
template <long _Np>
using make_index_sequence = __make_integer_sequence<long, _Np>;
template <class...> struct tuple {};
template <class> struct tuple_size;
template <class... _Tp>
struct tuple_size<tuple<_Tp...>> : integral_constant<sizeof...(_Tp)> {};
template <class _Tp> constexpr long tuple_size_v = tuple_size<_Tp>::value;
template <class _Op, class... _Bound> struct __perfect_forward_impl;
template <class _Op, long... _Idx, class... _Bound>
struct __perfect_forward_impl<_Op, index_sequence<_Idx...>, _Bound...> {
  __perfect_forward_impl() {}
  static const int value = 100 + sizeof...(_Idx) * 10 + sizeof...(_Bound);
};
template <class _Op, class... _Args>
using __perfect_forward =
    __perfect_forward_impl<_Op, make_index_sequence<sizeof...(_Args)>, _Args...>;
template <long _NBound, class = make_index_sequence<_NBound>>
struct __bind_back_op;
template <long _NBound, long... _Ip>
struct __bind_back_op<_NBound, index_sequence<_Ip...>> {};
template <class _Fn, class _BoundArgs>
struct __bind_back_t
    : __perfect_forward<__bind_back_op<tuple_size_v<_BoundArgs>>, _Fn, _BoundArgs> {
  using __perfect_forward<__bind_back_op<tuple_size_v<_BoundArgs>>, _Fn,
                          _BoundArgs>::__perfect_forward;
};
struct F {};
int main() {
  __bind_back_t<F, tuple<>> b;
  __CPROVER_assert(
    __perfect_forward_impl<int, index_sequence<0, 1>>::value == 120, "pf");
  return 0;
}
