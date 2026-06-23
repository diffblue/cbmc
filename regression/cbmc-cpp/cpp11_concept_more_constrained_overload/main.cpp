// N5008 [temp.constr.order] + [over.match.best]/2.6: when two function-template
// overloads are otherwise indistinguishable, the more-constrained one is
// chosen.  Cheap subsumes Cheap||Rare (a constraint subsumes a disjunction
// containing it), so f<Cheap> is more constrained than f<CheapOrRare> and must
// be selected for an int argument, returning 1.  A conforming compiler (g++)
// selects f<Cheap> and returns 1.
//
// KNOWNBUG: CBMC selects the LESS-constrained f<CheapOrRare> and returns 2.
//
// Root cause (traced): the two overloads have otherwise-identical signatures
// `f(T) -> int`, differing only in their concept constraint.  Their
// instantiations for `int` collide on a single instance symbol
// `f<signed_int>(signed_int)`, so only one candidate ever reaches overload
// disambiguation (instrumentation shows a single candidate, not two).  The
// constraint-subsumption ordering ([temp.constr.order]/1: decompose to atomic
// constraints, P subsumes Q iff every DNF clause of P meets every CNF clause of
// Q) therefore never runs.  Fixing this requires BOTH (a) concept-constrained
// overloads with the same signature forming a proper overload set (distinct
// instances), and (b) constraint-subsumption ordering to pick the
// more-constrained candidate.
//
// Flip to CORE once the more-constrained overload wins: assertion 1 must
// SUCCEED and assertion 2 (a wrong value) must FAIL, proving non-vacuity.
template <typename T>
concept Cheap = sizeof(T) >= 1;
template <typename T>
concept Rare = sizeof(T) >= 1000;
template <typename T>
concept CheapOrRare = Cheap<T> || Rare<T>;

template <Cheap T>
int f(T)
{
  return 1; // more constrained: Cheap subsumes Cheap||Rare
}
template <CheapOrRare T>
int f(T)
{
  return 2; // less constrained
}

int main()
{
  int r = f(0);
  __CPROVER_assert(r == 1, "more-constrained overload must win");
  __CPROVER_assert(r == 99, "WRONG (must FAIL)");
}
