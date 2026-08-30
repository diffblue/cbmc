/// \file
/// Exercises incremental SAT solving with MiniSat's simplifier. Under
/// --arrays-uf-always the variable-length array `a` uses the unbounded (U_ALL)
/// array encoding, whose Ackermann-style array-constraint refinement issues
/// many incremental SAT calls in the all-properties verification loop.
/// Together with the default array-bounds checks on the VLA, this drives the
/// repeated solves that, when MiniSat re-runs variable elimination before each
/// of them, can blow up into a hang. That hang was observed in conjunction
/// with the reduced Ackermann-constraint encoding for weak array equivalence
/// and a 32-bit target; the accompanying fix limits the simplifier to the
/// first solve. See test.desc for details.
int main()
{
  unsigned long array_size;
  int a[array_size];
  int i0, i1, i2, i3, i4;

  a[i0] = 0;
  a[i1] = 1;
  a[i2] = 2;
  a[i3] = 3;
  a[i4] = 4;

  __CPROVER_assert(a[i0] >= 0, "a[i0] >= 0");
  return 0;
}
