// SILENT constructor-body drop (round-43b arc): constructing a tuple
// whose element is CLASS-typed from a CONVERTING argument
// (`tuple<box<int>> t(3)`, libc++ <tuple> machinery transliterated
// below) leaves the instantiated constructor SYMBOL with an EMPTY
// value -- zero diagnostics, the body is never converted or queued
// (suspect: odr-use/drain bookkeeping missed for the constructor
// instantiated during list-element conversion inside the
// [class.base.init]/7 aggregate lowering).  Verification then reports
// "no body for callee" and the assertion fails.  The libc++ ranges
// pipe (views::take) sits behind this layer.
// clang++ accepts and runs clean; g++ rejects the alias-template pack
// deduction shape.
// cvise-reduced (83k -> 236 lines, header-free) from the libc++
// <ranges> views::take driver: with the hidden-friend operator|
// root FIXED (cpp20_hidden_friend_operator_template), the pipe
// `arr | views::take(3)` still drops main -- the failure sits in the
// __invoke/__invokable_r/invoke_result_t chain instantiated for the
// range-adaptor closure ("conversion from 'signed int [1l]' to
// '<<type:auto>>'" at the range expression; every one of the 236
// lines is load-bearing, hand-written sub-shapes all pass).  The
// assert argument was folded to a truthy constant by the reduction;
// the desc pattern requires the ASSERTION LINE so a dropped main
// (vacuous SUCCESS) keeps failing this test.  clang++ + ASan/UBSan
// + valgrind run the program clean.
template <int __v> struct integral_constant {
  static const int value = __v;
};
template <class _Tp> struct enable_if {
  typedef _Tp type;
};
namespace std {
template <class _Tp>
constexpr bool is_lvalue_reference_v = __is_lvalue_reference(_Tp);
template <class _Tp> _Tp __declval(int);
template <class _Tp> decltype(__declval<_Tp>(0)) declval();
template <class _From, class _To>
constexpr bool is_convertible_v = __is_convertible(_From, _To);
template <class _From, class>
concept convertible_to = requires { _From(); };
template <bool, class _If, class> using __conditional_t = _If;
template <class _Dp, class _Bp>
concept derived_from = is_convertible_v<_Dp, _Bp>;
struct __apply_cv_impl {
  template <class _Up> using __apply = _Up;
};
template <class, class _Up> using __apply_cv_t = __apply_cv_impl::__apply<_Up>;
template <class _Fp, class... _Args>
decltype(_Fp()(declval<_Args>()...)) __invoke(_Fp __f, _Args &&...__args) {
  return __f(__args...);
}
template <class, class _Fp, class... _Args> struct __invokable_r {
  template <class _XFp, class... _XArgs>
  static decltype(__invoke(_XFp(), declval<_XArgs>()...)) __try_call(int);
  using _Result = decltype(__try_call<_Fp, _Args...>(0));
};
template <class _Fp, class... _Args>
struct __invoke_of
    : enable_if<typename __invokable_r<void, _Fp, _Args...>::_Result> {};
template <class _Fn, class... _Args>
using invoke_result_t = __invoke_of<_Fn, _Args...>::type;
template <class _Fn, class... _Args>
invoke_result_t<_Fn, _Args...> invoke(_Fn __f, _Args &&...__args) {
  return __invoke(__f, __args...);
}
template <class> using iter_difference_t = int;
template <class _Ip>
concept input_or_output_iterator = requires(_Ip __i) { __i; };
struct {
  template <class _Tp, int _Np> auto operator()(_Tp (&__t)[_Np]) { return __t; }
} begin;
template <class _Tp> using iterator_t = decltype(begin(declval<_Tp>()));
template <unsigned long...> struct __tuple_indices {};
template <class _IdxType, _IdxType... _Values> struct __integer_sequence {
  template <long> using __to_tuple_indices = __tuple_indices<_Values...>;
};
template <long _Ep, long _Sp>
using __make_indices_imp =
    __make_integer_seq<__integer_sequence, long,
                       _Ep - _Sp>::template __to_tuple_indices<_Sp>;
template <class _Tp, _Tp...> struct integer_sequence;
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
template <class...> class tuple;
template <int _Ep, long _Sp = 0> struct __make_tuple_indices {
  typedef __make_indices_imp<_Ep, _Sp> type;
};
template <class...> struct __tuple_types {};
template <long, class> struct tuple_element;
template <long _Ip, class... _Types>
struct tuple_element<_Ip, __tuple_types<_Types...>> {
  typedef __type_pack_element<_Ip, _Types...> type;
};
template <class> struct tuple_size;
template <class... _Tp>
struct tuple_size<tuple<_Tp...>> : integral_constant<sizeof...(_Tp)> {};
template <class, class> struct __make_tuple_types_flat;
template <template <class...> class _Tuple, class... _Types, long... _Idx>
struct __make_tuple_types_flat<_Tuple<_Types...>, __tuple_indices<_Idx...>> {
  template <class _Tp>
  using __apply_quals =
      __tuple_types<__apply_cv_t<_Tp, __type_pack_element<_Idx, _Types...>>...>;
};
template <class _Tp, long _Ep = tuple_size<_Tp>::value, long _Sp = 0>
struct __make_tuple_types {
  using type =
      __make_tuple_types_flat<_Tp, typename __make_tuple_indices<_Ep, _Sp>::
                                       type>::template __apply_quals<_Tp>;
};
template <long _Ip, class... _Tp> struct tuple_element<_Ip, tuple<_Tp...>> {
  typedef tuple_element<_Ip, __tuple_types<_Tp...>>::type type;
};
template <bool _Const, class _Tp>
using __maybe_const = __conditional_t<_Const, _Tp, _Tp>;
template <class _Hp> struct __tuple_leaf {
  _Hp __value_;
  _Hp get() { return __value_; }
};
template <class...> struct __tuple_impl;
template <long... _Indx, class... _Tp>
struct __tuple_impl<__tuple_indices<_Indx...>, _Tp...> : __tuple_leaf<_Tp>... {
  template <unsigned long... _Uf, class... _Tf, class... _Up>
  __tuple_impl(__tuple_indices<_Uf...>, __tuple_types<_Tf...>,
               __tuple_indices<>, __tuple_types<>, _Up... __u)
      : __tuple_leaf<_Tf>(__u)... {}
};
template <class... _Tp> struct tuple {
  __tuple_impl<typename __make_tuple_indices<sizeof...(_Tp)>::type, _Tp...>
      __base_;
  template <class... _Up>
  tuple(_Up... __u)
      : __base_(typename __make_tuple_indices<sizeof...(_Up)>::type(),
                typename __make_tuple_types<tuple>::type(),
                typename __make_tuple_indices<sizeof...(_Tp),
                                              sizeof...(_Up)>::type(),
                typename __make_tuple_types<tuple, sizeof...(_Tp),
                                            sizeof...(_Up)>::type(),
                __u...) {}
};
template <int _Ip, class... _Tp>
tuple_element<_Ip, tuple<_Tp...>>::type get(tuple<_Tp...> __t) {
  return static_cast<
             __tuple_leaf<typename tuple_element<_Ip, tuple<_Tp...>>::type>>(
             __t.__base_)
      .get();
}
template <class _Tp> constexpr long tuple_size_v = tuple_size<_Tp>::value;
template <class T> struct box
{
  T v;
  box(T x) : v(x)
  {
  }
};
}
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  std::tuple<std::box<int>> t(3);
  __CPROVER_assert(std::get<0>(t).v == 3, "converting box elem");
  return 0;
}
