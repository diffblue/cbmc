// N5008 [class.conv.ctor]/1, [over.match.copy]/1.1: an explicit
// constructor -- also an explicit constructor template -- is not a
// converting constructor, so `f(i)' cannot initialize the `const loopt &'
// parameter and `f(citer)' (via iter's conversion function) is the only
// viable candidate.  The explicit flag of a constructor template's instance
// was not seen, `f(const loopt &)' was selected, or the call was ambiguous
// (analyses' loop_templatet(InstructionSet &&) vs a const_targett
// parameter; CBMC's own acceleration_utils.cpp, dog-fooding).
extern "C" void __CPROVER_assert(bool, const char *);
struct loopt
{
  int n = 0;
  loopt() = default;
  template <typename S>
  explicit loopt(S &&s) : n(1)
  {
  }
};
struct citer
{
  int v;
};
struct iter
{
  int v;
  operator citer() const
  {
    return citer{v};
  }
};
int f(const loopt &)
{
  return 1;
}
int f(citer c)
{
  return 10 + c.v;
}
int main()
{
  iter i{3};
  // N5008 [over.match.copy]/1.1, [over.best.ics]: an explicit constructor
  // is not a converting constructor; `f(i)' cannot initialize `const loopt &'
  __CPROVER_assert(f(i) == 13, "explicit constructor template not viable");
  loopt l{i};
  __CPROVER_assert(l.n == 1, "direct-initialization uses it");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
