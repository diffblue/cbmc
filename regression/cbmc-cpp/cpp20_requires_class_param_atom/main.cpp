// N5008 [temp.constr.decl]/1 + [temp.deduct]/5: after deduction, a
// function template candidate whose associated constraints are not
// satisfied is removed from the overload set.  Here the constrained
// converting constructor deduces U2 = int for the argument 0, and
// __is_constructible(nodet*, int) is FALSE (an int prvalue is not a
// null pointer constant, [conv.ptr]/1), so the constrained candidate
// must be removed and pr(const T2&) selected -- for which the literal 0
// IS a null pointer constant.
//
// KNOWNBUG: the requires-clause satisfaction check cannot evaluate an
// atom that references the ENCLOSING CLASS's template parameter (T2):
// the evaluator substitutes only the member template's own parameters
// (U2), leaves the atom "unknown", conservatively keeps the candidate,
// and the wrongly-selected constructor's body then fails conversion
// ("invalid implicit conversion from 'signed int' to 'struct nodet*'";
// silently nil'd for system headers).  This is the residual behind
// cpp20_pair_converting_ctor / cpp20_map_basic: libstdc++ C++20 pair's
// requires(_S_constructible<_U1, _U2>()) expands to exactly such atoms.
// The same shape with a NON-template class (T2 spelled concretely)
// works.
//
// g++/clang++ verify at runtime.  Flip to CORE when fixed.
extern "C" void __CPROVER_assert(bool, const char *);

struct nodet
{
  int v;
};

template <class T2>
struct pr
{
  T2 second;
  pr(const T2 &b) : second(b)
  {
  }
  template <class U2 = T2>
    requires(__is_constructible(T2, U2))
  pr(U2 &&b) : second(static_cast<U2 &&>(b))
  {
  }
};

int main()
{
  pr<nodet *> b(0);
  __CPROVER_assert(b.second == nullptr, "null pointer constant selected");
  return 0;
}
