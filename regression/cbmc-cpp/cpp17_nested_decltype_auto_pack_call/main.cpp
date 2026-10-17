// N5008 [dcl.spec.auto]/3-4,11 + [temp.variadic]/4-5: a function template with
// a DEDUCED return type (`decltype(auto)`) whose body calls ANOTHER function
// template that itself has a deduced return type, passing a MULTI-element
// non-type parameter pack as the call arguments:
//
//   decltype(auto) apply_impl(seq<V...>) { return invoke(V...); }
//                                                  ^^^^^^^^^^^  invoke is also
//                                                               decltype(auto)
//
// mirrors libstdc++ std::apply's `__apply_impl` -> `std::__invoke`.
//
// CORE (was KNOWNBUG): the caller's return type was left an unresolved
// `<<type:decltype>>`.  Root cause: the eager auto/decltype(auto)
// convert_function pack expansion ran on the inner callee's body while the
// OUTER instantiation's template_map was still active, re-expanding the
// callee's (already-expanded) function-parameter pack against the outer pack's
// size and corrupting `add(a$0, a$1)` into `add(a$0, a$0)`.  Fixed by expanding
// ONLY the non-type call-argument pack (from pack_expr_map) in that eager path,
// leaving value / function-parameter pack expansions untouched.
//
// g++ and clang++ compute the same values.  Non-vacuous: the returned value is
// a concrete function of the deduced pack, never checked under the old
// incomplete-body behaviour.

extern "C" void __CPROVER_assert(int, const char *);

int add(int a, int b)
{
  return a + b;
}

int add3(int a, int b, int c)
{
  return a + b + c;
}

template <class... A>
decltype(auto) invoke(A... a)
{
  return add(a...);
}

template <class... A>
decltype(auto) invoke3(A... a)
{
  return add3(a...);
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

template <int... V>
decltype(auto) apply_impl3(seq<V...>)
{
  return invoke3(V...);
}

int main()
{
  __CPROVER_assert(apply_impl(seq<1, 2>{}) == 3, "nested add(1,2)==3");
  __CPROVER_assert(apply_impl3(seq<4, 5, 6>{}) == 15, "nested add3(4,5,6)==15");
  return 0;
}
