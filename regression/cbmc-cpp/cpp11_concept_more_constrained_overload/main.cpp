// N5008 [temp.constr.order] + [over.match.best]/2.6: when two function-template
// overloads are otherwise indistinguishable, the more-constrained one is
// chosen.  Cheap subsumes Cheap||Rare (a constraint subsumes a disjunction
// containing it), so f<Cheap> is more constrained than f<CheapOrRare> and must
// be selected for an int argument, returning 1 (matching g++).
//
// This is selected by the pre-instantiation concept-subsumption filter in
// cpp_typecheck_resolvet::resolve, which now compares the normal forms of the
// associated constraints ([temp.constr.order]/1: decompose to atomic
// constraints; P subsumes Q iff every DNF clause of P meets every CNF clause of
// Q) instead of a textual comparison of constraint names.  Filtering to the
// more-constrained template before instantiation also avoids the otherwise
// colliding instance symbols of the two same-signature overloads.
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
