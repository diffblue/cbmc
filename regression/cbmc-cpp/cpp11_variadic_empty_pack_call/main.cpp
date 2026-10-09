// C++ [temp.variadic]/5: a pack expansion `pattern...` expands into a list of
// zero or more instantiations of the pattern.  When the pack is empty the list
// is empty, so `f(a...)` with an empty `a` is the call `f()`.
//
// KNOWNBUG: an empty parameter pack expanded in a function-call argument list is
// not handled -- the call `base(a...)` with zero pack elements fails to resolve
// ("found no match for symbol 'base'") instead of calling base().  Reclassify
// CORE once empty pack expansions produce an empty argument list.

int base()
{
  return 42;
}

template <typename... A>
int call0(A... a)
{
  return base(a...); // empty pack -> base()
}

int main()
{
  __CPROVER_assert(call0() == 42, "empty-pack call expands to base()");
  return 0;
}
