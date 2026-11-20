// N5008 [expr.cond]/4.1: when the second and third operands are lvalues of
// class types of which one is a base of the other, the derived operand is
// converted to an lvalue of the base type by binding to its base
// subobject, and the result is that lvalue -- `flag ? gb : d' (base,
// derived) designates d's base subobject.  The front end reported "types
// are incompatible" (`std::ostream &out(b ? std::cout : file)' with an
// ofstream file, CBMC's own goto_analyzer_parse_options.cpp, dog-fooding).
extern "C" void __CPROVER_assert(bool, const char *);
struct base
{
  int v = 1;
};
struct derived : base
{
  int w = 2;
};
base gb;
int main()
{
  bool flag = false;
  derived d;
  d.v = 5;
  base &r = flag ? gb : d; // [expr.cond]/4.1: lvalue base
  r.v = 7;
  __CPROVER_assert(d.v == 7, "conditional binds to the base subobject of d");
  const base &cr = flag ? d : gb;
  __CPROVER_assert(cr.v == 1, "other order");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
