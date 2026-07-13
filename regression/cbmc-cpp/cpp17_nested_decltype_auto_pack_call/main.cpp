// N5008 [dcl.spec.auto]/3-4,11 + [temp.variadic]/4-5: the minimal core of the
// std::apply blocker.  A function template with a DEDUCED return type
// (`decltype(auto)`) whose body calls ANOTHER function template that itself has
// a deduced return type, passing a MULTI-element non-type parameter pack as the
// call arguments:
//
//   decltype(auto) apply_impl(seq<V...>) { return invoke(V...); }
//                                                  ^^^^^^^^^^^  invoke is also
//                                                               decltype(auto)
//
// This mirrors libstdc++ std::apply exactly:
//   __apply_impl(...) -> decltype(auto) { return std::__invoke(f, get<Idx>(t)...); }
//   std::__invoke(...) -> decltype(auto) { ... }
//
// KNOWNBUG: CBMC leaves the caller's return type an unresolved
// `<<type:decltype>>` -- "invalid implicit conversion from '<<type:decltype>>'
// to 'signed int'" and "could not fully type-check 'main'" -- so the call is
// unsound.  This is the exact error of cpp17_apply_basic.
//
// It requires ALL of: (1) the OUTER return type is deduced (auto/decltype(auto),
// not a trailing decltype); (2) the INNER callee is a TEMPLATE with a deduced
// return type (a concrete decltype(auto) function works); (3) the pack has MORE
// THAN ONE element (a single-element pack works).  A deduced return type over a
// pack call to a *known* function is handled (cpp11_auto_return_deduce_pack_call,
// CORE); the gap is the nested deduced-return callee whose return type must be
// deduced during the outer function's own return-type deduction.
//
// g++ compiles and runs r == 3; clang++ accepts.  Flip to CORE once nested
// deduced-return instantiation during return-type deduction is supported.

extern "C" void __CPROVER_assert(int, const char *);

int add(int a, int b)
{
  return a + b;
}

template <class... A>
decltype(auto) invoke(A... a)
{
  return add(a...);
}

template <int...>
struct seq
{
};

template <int... V>
decltype(auto) apply_impl(seq<V...>)
{
  return invoke(V...);
}

int main()
{
  int r = apply_impl(seq<1, 2>{});
  __CPROVER_assert(r == 3, "nested decltype(auto) pack call yields 3");
  __CPROVER_assert(r != 3, "WRONG must FAIL");
  return 0;
}
