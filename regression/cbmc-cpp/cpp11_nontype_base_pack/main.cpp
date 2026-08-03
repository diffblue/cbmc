// cvise-reduced from the libc++ <tuple> driver (cpp11_libcxx_tuple):
// a partial specialization deriving from a base pack over its
// LEADING NON-TYPE pack (`__tuple_impl<__tuple_indices<_Indx...>,
// _Tp...> : __tuple_leaf<_Indx>...`, [temp.variadic]/5.2).  The
// instance is built with ZERO bases and zero components, so get()'s
// member access reads outside the object.  The TYPE-pack analogue
// (`: leaf<T>...`, cpp11_tuple_leaf_no_body) is fixed; the non-type
// element recovery for a non-identity partial-spec pattern is the
// residual.  clang++ (clang builtins) accepts and runs clean.
extern "C" void __CPROVER_assert(bool, const char *);
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
  template <class> using __apply_quals = __tuple_types<>;
};
template <long _Sp = 0> struct __make_tuple_types {
  using type =
      __make_tuple_types_flat<tuple<>,
                              typename __make_tuple_indices<_Sp>::type>::
          template __apply_quals<tuple<>>;
};
template <long _Ip, class... _Tp> struct tuple_element<_Ip, tuple<_Tp...>> {
  typedef tuple_element<_Ip, __tuple_types<_Tp...>>::type type;
};
template <int> struct __tuple_leaf {
  int __value_;
  template <class _Tp> __tuple_leaf(_Tp __t) : __value_(__t) {}
  int get() { return __value_; }
};
template <class...> struct __tuple_impl;
template <long... _Indx, class... _Tp>
struct __tuple_impl<__tuple_indices<_Indx...>, _Tp...>
    : __tuple_leaf<_Indx>... {
  template <unsigned long... _Uf, class... _Up>
  __tuple_impl(__tuple_indices<_Uf...>, __tuple_types<>, __tuple_indices<>,
               __tuple_types<>, _Up... __u)
      : __tuple_leaf<_Uf>(__u)... {}
};
template <class... _Tp> struct tuple {
  __tuple_impl<typename __make_tuple_indices<sizeof...(_Tp)>::type> __base_;
  template <class... _Up>
  tuple(_Up... __u)
      : __base_(typename __make_tuple_indices<sizeof...(_Up)>::type(),
                __make_tuple_types<>::type(),
                typename __make_tuple_indices<sizeof...(_Tp), 1>::type(),
                __make_tuple_types<>::type(), __u...) {}
};
template <int _Ip, class... _Tp>
tuple_element<_Ip, tuple<_Tp...>>::type get(tuple<_Tp...> __t) {
  return __t.__base_.get();
}
tuple<int> main_t(1);
int main() { __CPROVER_assert(get<0>(main_t), "first"); }
