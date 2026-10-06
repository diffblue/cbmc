// N5008 [expr.new]/24, [dcl.init.general]/16.5: `new T[n](e1, ..., ek)'
// copy-initializes the first k elements from the expression-list and
// value-initializes the rest
extern "C" void __CPROVER_assert(bool, const char *);
struct C
{
  int v;
  C() : v(7)
  {
  }
  C(int x) : v(x)
  {
  }
};
struct P
{
  int x;
  int y;
};
int main()
{
  int *a = new int[3](1, 2);
  __CPROVER_assert(a[0] == 1 && a[1] == 2 && a[2] == 0, "parenthesized");
  C *c = new C[3](5);
  __CPROVER_assert(c[0].v == 5 && c[1].v == 7 && c[2].v == 7, "class");
  P *p = new P[2](P{1, 2});
  __CPROVER_assert(p[0].y == 2 && p[1].x == 0, "aggregate");
  __CPROVER_assert(a[2] == 1, "WRONG (must FAIL)");
}
