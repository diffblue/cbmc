// The remaining cpp17_apply_basic blocker: a function template with a DEDUCED
// return type (`decltype(auto)`) whose body expands a pack of REAL std::get
// calls into another call:  `return add(std::get<I>(t)...)`.  This is the shape
// of libstdc++ std::apply's __apply_impl:
//   return std::__invoke(f, std::get<_Idx>(t)...);
//
// KNOWNBUG: CBMC fails to deduce the return type -- "could not fully type-check
// 'main'" (in cpp17_apply_basic this surfaces as the unresolved
// `<<type:decltype>>` return type of std::apply).  Hand-written stand-ins for
// std::get (a plain get returning a reference, a get with a deduced
// `decltype(auto)` return, a trait-based get) are all handled
// (cpp11_.../cpp17_nested_decltype_auto_pack_call, CORE); the defect is specific
// to the REAL std::get, whose overloaded (&, const&, &&) / tuple_element-based
// return type must be resolved for each pack element inside the enclosing
// decltype(auto) deduction.
//
// The tuple is taken by reference here, so this is independent of the separate
// std::get-by-value-copy value bug (a std::tuple passed by value to a template
// then read by std::get yields garbage -- cpp17_tuple_basic territory).
//
// g++ compiles and runs r == 3; clang++ accepts.  Flip to CORE once
// decltype(auto) return deduction over a real std::get pack expansion works.
//
// Non-vacuous: assertion 2 ("WRONG must FAIL") must FAIL once the return type is
// deduced and the body really type-checked.

#include <tuple>

extern "C" void __CPROVER_assert(int, const char *);

int add(int a, int b)
{
  return a + b;
}

template <class T, unsigned long... I>
decltype(auto) apply_impl(T &t, std::index_sequence<I...>)
{
  return add(std::get<I>(t)...);
}

int main()
{
  std::tuple<int, int> t{1, 2};
  int r = apply_impl(t, std::index_sequence<0, 1>{});
  __CPROVER_assert(r == 3, "decltype(auto) over std::get pack: 1+2==3");
  __CPROVER_assert(r != 3, "WRONG must FAIL");
  return 0;
}
