// Transliterated libc++ <tuple> constructor machinery (__tuple_indices /
// __make_tuple_types / __tuple_impl / tuple), the shape behind
// std::ranges pipe closures under --stdlib libc++.  Exercises, in one
// kernel: [temp.deduct] two-pack constructor deduction against COMPUTED
// empty-suffix arguments, [temp.variadic]/5 lockstep base/mem-init pack
// expansion (`__tuple_leaf<_Tf>{__u}...`), and [class.base.init]/7
// aggregate base initialization from an instantiated ctor template.
// g++ rejects the alias-template pack deduction shape; clang accepts.
extern "C" void __CPROVER_assert(bool, const char *);
template <unsigned long...> struct __tuple_indices
{
};
template <class... _Tp> struct __tuple_types
{
};
template <class _IdxType, _IdxType... _Values> struct __integer_sequence
{
  template <unsigned long _Sp>
  using __to_tuple_indices = __tuple_indices<(_Values + _Sp)...>;
};
template <unsigned long _Ep, unsigned long _Sp = 0>
using __make_tuple_indices_t =
  typename __make_integer_seq<__integer_sequence, unsigned long, _Ep - _Sp>::
    template __to_tuple_indices<_Sp>;
template <unsigned long _Ep, unsigned long _Sp = 0>
struct __make_tuple_indices
{
  typedef __make_tuple_indices_t<_Ep, _Sp> type;
};
template <class _Tp, class _Up> struct __apply_cv
{
  typedef _Up type;
};
template <class _Tp, class _Up>
using __apply_cv_t = typename __apply_cv<_Tp, _Up>::type;
template <class _TupleTypes, class _Idxs> struct __make_tuple_types_flat;
template <template <class...> class _Tuple, class... _Types,
          unsigned long... _Idx>
struct __make_tuple_types_flat<_Tuple<_Types...>, __tuple_indices<_Idx...>>
{
  template <class _Tp>
  using __apply_quals =
    __tuple_types<__apply_cv_t<_Tp, __type_pack_element<_Idx, _Types...>>...>;
};
template <class _Tp, unsigned long _Ep, unsigned long _Sp = 0>
struct __make_tuple_types
{
  static_assert(_Sp <= _Ep, "");
  typedef typename __make_tuple_types_flat<
    _Tp, typename __make_tuple_indices<_Ep, _Sp>::type>::
    template __apply_quals<_Tp>
      type;
};
template <class _Hp> struct __tuple_leaf
{
  _Hp __value_;
  _Hp get()
  {
    return __value_;
  }
};
template <class...> struct __tuple_impl;
template <unsigned long... _Indx, class... _Tp>
struct __tuple_impl<__tuple_indices<_Indx...>, _Tp...> : __tuple_leaf<_Tp>...
{
  template <unsigned long... _Uf, class... _Tf, class... _Up>
  __tuple_impl(
    __tuple_indices<_Uf...>,
    __tuple_types<_Tf...>,
    __tuple_indices<>,
    __tuple_types<>,
    _Up... __u)
    : __tuple_leaf<_Tf>{__u}...
  {
  }
};
template <class... _Tp> struct tuple
{
  __tuple_impl<typename __make_tuple_indices<sizeof...(_Tp)>::type, _Tp...>
    __base_;
  template <class... _Up>
  tuple(_Up... __u)
    : __base_(
        typename __make_tuple_indices<sizeof...(_Up)>::type(),
        typename __make_tuple_types<tuple, sizeof...(_Up)>::type(),
        typename __make_tuple_indices<sizeof...(_Tp), sizeof...(_Up)>::type(),
        typename __make_tuple_types<tuple, sizeof...(_Tp), sizeof...(_Up)>::
          type(),
        __u...)
  {
  }
};
int main()
{
  tuple<char, long> t('a', 2L);
  __CPROVER_assert(
    static_cast<__tuple_leaf<long> &>(t.__base_).get() == 2L,
    "libcxx tuple ctor");
  return 0;
}
