// N5008 [temp.deduct]/2,5 + [dcl.type.simple]/4 + [temp.variadic]/4-5: a
// function template whose TRAILING RETURN TYPE is a `decltype` of a CALL with a
// pack expansion, `-> decltype(add(I...))`, must have that return type computed
// (with `I...` expanded) during deduction/overload resolution.  This is exactly
// the shape of libstdc++ std::apply's helper:
//   template<class _Fn, class _Tuple, size_t... _Idx>
//   constexpr decltype(auto)
//   __apply_impl(_Fn&& __f, _Tuple&& __t, index_sequence<_Idx...>)
//   { return std::__invoke(std::forward<_Fn>(__f),
//                          std::get<_Idx>(std::forward<_Tuple>(__t))...); }
// whose result type is `decltype(__invoke(f, get<_Idx>(t)...))`.
//
// KNOWNBUG: CBMC fails to resolve such a function template -- "found no match
// for symbol 'impl'" -- so the call is left untyped and the enclosing body is
// not fully type-checked.  A `decltype` of a call with FIXED arguments
// (`-> decltype(add(1,2))`), and a plain `auto` / `decltype(auto)` return whose
// body simply forwards, are all handled correctly, so the defect is specific to
// a decltype return type that contains a PACK EXPANSION in the call.  g++ and
// clang++ compute r == 3.
//
// This is the core of cpp17_apply_basic (std::apply(add, make_tuple(1,2))): a
// separate layer from the std::tuple construction bugs.  Flip to CORE once a
// decltype-return-type over a pack-expansion call is resolved.
// Non-vacuity: assertion 2 ("WRONG must FAIL") must FAIL when the fix lands.

extern "C" void __CPROVER_assert(int, const char *);

int add(int a, int b)
{
  return a + b;
}

template <int...>
struct seq
{
};

template <int... I>
auto impl(seq<I...>) -> decltype(add(I...))
{
  return add(I...);
}

int main()
{
  int r = impl(seq<1, 2>{});
  __CPROVER_assert(r == 3, "decltype-return pack call yields 3");
  __CPROVER_assert(r != 3, "WRONG must FAIL");
  return 0;
}
