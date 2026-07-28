// Header-free mimic of libc++ std::tuple (cvise-reduced from a
// <tuple> driver; gates cpp11_libcxx_tuple and the test_libcxx variants
// of cpp11_tuple_basic / cpp17_tuple_basic / cpp17_apply_basic).
// The tuple constructor chain routes through __make_integer_seq /
// __type_pack_element metafunctions; the instantiated member bodies
// are lost ("no body for callee tuple/get") although the source
// defines them.  clang++ (libc++ shape) accepts and runs clean; the
// metafunction builtins are clang-only, g++ does not apply.

namespace std {
inline namespace __1 {
struct __apply_cv_impl {
  template <class _Up> using __apply = _Up;
};
template <class, class _Up> using __apply_cv_t = __apply_cv_impl::__apply<_Up>;
template <class...> class tuple;
template <unsigned long...> struct __tuple_indices {};
template <class _IdxType, _IdxType... _Values> struct __integer_sequence {
  template <long> using __to_tuple_indices = __tuple_indices<_Values...>;
};
template <long _Ep, long _Sp>
using __make_indices_imp =
    __make_integer_seq<__integer_sequence, long,
                       _Ep - _Sp>::template __to_tuple_indices<_Sp>;
template <int _Ep, long _Sp = 0> struct __make_tuple_indices {
  typedef __make_indices_imp<_Ep, _Sp> type;
};
template <class...> struct __tuple_types {};
template <long, class> struct tuple_element;
template <long _Ip, class... _Types>
struct tuple_element<_Ip, __tuple_types<_Types...>> {
  typedef __type_pack_element<_Ip, _Types...> type;
};
template <class, class> struct __make_tuple_types_flat;
template <template <class...> class _Tuple, class... _Types, long... _Idx>
struct __make_tuple_types_flat<_Tuple<_Types...>, __tuple_indices<_Idx...>> {
  template <class _Tp>
  using __apply_quals =
      __tuple_types<__apply_cv_t<_Tp, __type_pack_element<_Idx, _Types...>>...>;
};
template <class _Tp, int _Ep, long _Sp = 0> struct __make_tuple_types {
  using type =
      __make_tuple_types_flat<_Tp, typename __make_tuple_indices<_Ep, _Sp>::
                                       type>::template __apply_quals<_Tp>;
};
template <long _Ip, class... _Tp> struct tuple_element<_Ip, tuple<_Tp...>> {
  typedef tuple_element<_Ip, __tuple_types<_Tp...>>::type type;
};
template <class> struct __tuple_leaf {
  int __value_;
  template <class _Tp> __tuple_leaf(_Tp __t) : __value_(__t) {}
  int get() { return __value_; }
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
                typename __make_tuple_types<tuple, sizeof...(_Up)>::type(),
                typename __make_tuple_indices<sizeof...(_Tp), 1>::type(),
                typename __make_tuple_types<tuple, sizeof...(_Tp), 1>::type(),
                __u...) {}
};
template <int _Ip, class... _Tp>
tuple_element<_Ip, tuple<_Tp...>>::type get(tuple<_Tp...> __t) {
  return static_cast<
             __tuple_leaf<typename tuple_element<_Ip, tuple<_Tp...>>::type> &>(
             __t.__base_)
      .get();
}
} // namespace __1
} // namespace std

int main() {
  std::tuple<int> t(42);
  __CPROVER_assert(get<0>(t) == 42, "leaf value");
  return 0;
}
