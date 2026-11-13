// N5008 [expr.cond]/1, /7: only one of the second and third operands is
// evaluated; with class prvalue operands the result is a prvalue
// initialized from the selected one
extern "C" void __CPROVER_assert(bool, const char *);
int constructions = 0;
struct D
{
  int v;
  D(int x) : v(x)
  {
    ++constructions;
  }
};
int main(int argc, char **)
{
  bool b = argc > 1;
  D d = b ? D(1) : D(2);
  __CPROVER_assert(constructions == 1 && d.v == (b ? 1 : 2), "initializer");
  int v = (b ? D(3) : D(4)).v;
  __CPROVER_assert(constructions == 2 && v == (b ? 3 : 4), "member access");
  __CPROVER_assert(constructions == 4, "WRONG (must FAIL)");
}
