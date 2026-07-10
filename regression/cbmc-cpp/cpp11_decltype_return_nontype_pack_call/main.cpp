// N5008 [temp.deduct]/2,5 + [dcl.type.simple]/4 + [temp.variadic]/4-5: a
// function template whose TRAILING RETURN TYPE is a `decltype` of a CALL with a
// pack expansion, `-> decltype(add(I...))`, must have that return type computed
// (with `I...` expanded) during deduction/overload resolution, and its body
// call `add(I...)` must expand to the deduced pack's element values.  This is
// exactly the shape of libstdc++ std::apply's helper:
//   template<class _Fn, class _Tuple, size_t... _Idx>
//   constexpr decltype(auto)
//   __apply_impl(_Fn&& __f, _Tuple&& __t, index_sequence<_Idx...>)
//   { return std::__invoke(std::forward<_Fn>(__f),
//                          std::get<_Idx>(std::forward<_Tuple>(__t))...); }
// whose result type is `decltype(__invoke(f, get<_Idx>(t)...))`.
//
// CORE (was KNOWNBUG): CBMC previously failed to resolve such a function
// template ("found no match for symbol 'impl'").  Fixed by (1) recording a
// deduced non-type pack's element values in pack_expr_map (not shadowed by an
// empty pack_args_map entry), (2) expanding that pack to full arity in the
// guessed template arguments, and (3) expanding a non-type call-argument pack
// in both the decltype return type and the body.  g++ and clang++ compute the
// same values.
//
// Non-vacuous: the returned value is a concrete function of the deduced pack
// (3 / 6), which under the old behaviour was nondeterministic / a resolution
// failure.

extern "C" void __CPROVER_assert(int, const char *);

int add(int a, int b)
{
  return a + b;
}

int add3(int a, int b, int c)
{
  return a + b + c;
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

template <int... I>
auto impl3(seq<I...>) -> decltype(add3(I...))
{
  return add3(I...);
}

int main()
{
  __CPROVER_assert(impl(seq<1, 2>{}) == 3, "decltype-return add(1,2)==3");
  __CPROVER_assert(impl3(seq<1, 2, 3>{}) == 6, "decltype-return add3(1,2,3)==6");
  return 0;
}
