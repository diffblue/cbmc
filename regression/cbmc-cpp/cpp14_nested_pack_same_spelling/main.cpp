// N5008 [temp.variadic]/5 + [basic.scope.temp]: in the pattern
// `type_pack_element<_Idx, _Types...>...`, `_Types` is expanded by the
// NESTED expansion, so only `_Idx` governs the outer one; and the name
// `_Idx` denotes the template parameter found by lookup, even when an
// enclosing instantiation has a parameter of the SAME SPELLING (pf_impl's
// `_Idx...` around __make_tuple_types_flat's `_Idx...`, the libc++ tuple
// shape).  Pre-fix, spelling-based pack matching mixed the two `_Idx`
// packs (lengths 0 vs 2), refused to expand, and the scalar fallthrough
// resolved to the empty-pack sentinel ("symbol '_Idx' does not uniquely
// resolve: constructor void () / constructor void (void)").
// g++ rejects the alias-template pack deduction shape; clang accepts.
extern "C" void __CPROVER_assert(bool, const char *);
template <long...> struct tuple_indices
{
};
template <class _IdxType, _IdxType... _Values> struct integer_seq
{
  template <long> using to_indices = tuple_indices<_Values...>;
};
template <long _Ep, long _Sp>
using make_indices_imp =
  typename __make_integer_seq<integer_seq, long, _Ep - _Sp>::
    template to_indices<_Sp>;
template <class... T> struct tuple_types
{
  static const int size = sizeof...(T);
};
template <long _Idx, class... _Types>
using type_pack_element = __type_pack_element<_Idx, _Types...>;
template <class _TupleTypes, class _Idxs> struct make_tuple_types_flat;
// the outer expansion is governed by _Idx ONLY; _Types is consumed by
// the nested type_pack_element<_Idx, _Types...>
template <template <class...> class _Tuple, class... _Types, long... _Idx>
struct make_tuple_types_flat<_Tuple<_Types...>, tuple_indices<_Idx...>>
{
  using type = tuple_types<type_pack_element<_Idx, _Types...>...>;
};
template <class _Tp, long _Ep, long _Sp> struct make_tuple_types
{
  using type =
    typename make_tuple_types_flat<_Tp, make_indices_imp<_Ep, _Sp>>::type;
};
// another template whose pack is ALSO spelled _Idx: instantiated FIRST
// with a non-empty pack, leaving a same-spelling entry in the flat map
template <class _Op, class _Sq, class... _Bound> struct pf_impl;
template <class _Op, long... _Idx, class... _Bound>
struct pf_impl<_Op, tuple_indices<_Idx...>, _Bound...>
{
  // member function so elaboration binds _Idx in an enclosing scope
  static int probe()
  {
    return static_cast<int>(sizeof...(_Idx));
  }
  // the make_tuple_types use INSIDE the same instantiation, with an
  // EMPTY range (Ep == Sp) and a NON-EMPTY one
  using full = typename make_tuple_types<tuple_types<_Bound...>,
                                         static_cast<long>(sizeof...(_Bound)),
                                         0>::type;
  using empty = typename make_tuple_types<tuple_types<_Bound...>,
                                          2,
                                          2>::type;
};
int main()
{
  typedef pf_impl<int, tuple_indices<0, 1>, char, long> pf;
  __CPROVER_assert(pf::probe() == 2, "own pack");
  __CPROVER_assert(pf::full::size == 2, "full range");
  __CPROVER_assert(pf::empty::size == 0, "empty range");
  return 0;
}
