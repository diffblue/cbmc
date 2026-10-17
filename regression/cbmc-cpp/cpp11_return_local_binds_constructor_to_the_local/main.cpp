// N5008 [class.copy.elision]/3, [dcl.init.ref]/5.3.1: `return d;' for a
// local d selects the constructor treating d as an rvalue; the constructor's
// reference parameter binds to d itself -- no further object is created
extern "C" void __CPROVER_assert(bool, const char *);
int copies = 0, moves = 0, destructions = 0;
struct D
{
  int v;
  D(int x) : v(x)
  {
  }
  D(const D &o) : v(o.v)
  {
    ++copies;
  }
  D(D &&o) : v(o.v)
  {
    o.v = -1;
    ++moves;
  }
  ~D()
  {
    ++destructions;
  }
};
struct C
{
  int v;
  C(int x) : v(x)
  {
  }
  C(const C &o) : v(o.v)
  {
    ++copies;
  }
  ~C()
  {
    ++destructions;
  }
};
D local_d(int x)
{
  D d(x);
  return d;
}
C local_c(int x)
{
  C c(x);
  return c;
}
int main()
{
  {
    D b = local_d(3);
    __CPROVER_assert(b.v == 3, "moved value");
  }
  __CPROVER_assert(
    copies == 0 && moves <= 2 && destructions == 1 + moves, "move");
  {
    C c = local_c(4);
    __CPROVER_assert(c.v == 4, "copied value");
  }
  __CPROVER_assert(
    copies <= 2 && destructions == 2 + moves + copies,
    "copy without move constructor");
  __CPROVER_assert(destructions == 0, "WRONG (must FAIL)");
}
