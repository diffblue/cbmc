// N5008 [expr.eq]/3, [expr.type]/4: a pointer to a derived class and a
// pointer to its base are compared after converting both to the composite
// pointer type, the pointer to the base, which adjusts the derived pointer
// to its base subobject
extern "C" void __CPROVER_assert(bool, const char *);
struct L
{
  int l;
};
struct R
{
  int r;
};
struct M : L, R
{
};
int main()
{
  M m;
  R *pr = &m;
  const R *cpr = &m;
  __CPROVER_assert(pr == &m && &m == pr, "derived and base pointers");
  __CPROVER_assert(cpr == &m && !(cpr != &m), "with qualification");
  L *pl = &m;
  __CPROVER_assert(pl == &m, "first base");
  __CPROVER_assert(pr != &m, "WRONG (must FAIL)");
}
