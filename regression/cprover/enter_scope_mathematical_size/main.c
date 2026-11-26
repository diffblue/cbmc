int main()
{
  // A variable of a mathematical type (here: an unbounded integer) has no
  // statically computable byte size. The enter-scope-state term for it falls
  // back to a unit size rather than aborting; this is sound because such
  // objects are not byte-addressed. See state_encoding_smt2_convt::
  // add_converters (ID_enter_scope_state).
  __CPROVER_integer x;

  __CPROVER_assert(1, "reachable");
  return 0;
}
