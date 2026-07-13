// N5008 [temp.spec.partial] + [temp.variadic]/4-5: a VARIABLE TEMPLATE partial
// specialization whose pattern deduces a parameter PACK:
//
//   template <class T>    constexpr unsigned long tsize_v           = 99;
//   template <class... E> constexpr unsigned long tsize_v<tup<E...>> = sizeof...(E);
//
// This is exactly libstdc++'s std::tuple_size_v:
//   template<typename... _Types>
//     inline constexpr size_t tuple_size_v<tuple<_Types...>> = sizeof...(_Types);
// which std::apply uses to size its index sequence:
//   using _Indices = make_index_sequence<tuple_size_v<remove_reference_t<_Tuple>>>;
//
// KNOWNBUG: CBMC selects the partial specialization but collapses the deduced
// pack to ONE element: `tsize_v<tup<int,int>>` evaluates to 1 (not 2, not the
// primary's 99).  Confirmed: asserting ==1 SUCCEEDS while ==2 fails.  Through
// std::apply this sizes the index sequence wrongly, so the inner
// `__invoke(f, get<Idx>(t)...)` is called with the wrong arity and its
// decltype(auto) return type fails to resolve -- the residual
// "invalid implicit conversion from '<<type:decltype>>'" of cpp17_apply_basic.
//
// The CLASS-template analogue (tsize<tup<E...>>::value) is handled correctly;
// the defect is specific to a variable-template partial specialization with a
// pack.  g++ static_asserts and runs the value 2; clang++ accepts.  Flip to
// CORE once the pack is deduced with full arity.
//
// Non-vacuous: assertion 2 ("WRONG must FAIL") must FAIL once the pack has the
// correct arity.

extern "C" void __CPROVER_assert(int, const char *);

template <class...>
struct tup
{
};

template <class T>
constexpr unsigned long tsize_v = 99;

template <class... E>
constexpr unsigned long tsize_v<tup<E...>> = sizeof...(E);

int main()
{
  unsigned long v2 = tsize_v<tup<int, int>>;
  unsigned long v3 = tsize_v<tup<int, int, int>>;
  __CPROVER_assert(v2 == 2, "pack variable-template partial spec: size 2");
  __CPROVER_assert(v3 == 3, "pack variable-template partial spec: size 3");
  __CPROVER_assert(v2 != 2, "WRONG must FAIL");
  return 0;
}
