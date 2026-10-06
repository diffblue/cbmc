// N5008 [expr.new]/17, /24, [dcl.init.general]/9.3, [dcl.init.aggr]/4-5:
// `new T[n]()' and `new T[n]{}' value-initialize each element;
// `new T[n]{e1, ..., ek}' initializes the first k elements from the list and
// value-initializes the rest
extern "C" void __CPROVER_assert(bool, const char *);
struct S
{
  int i;
  long l;
};
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
int main()
{
  int *a = new int[3]();
  __CPROVER_assert(a[0] == 0 && a[2] == 0, "parentheses");
  int *b = new int[2]{};
  __CPROVER_assert(b[1] == 0, "empty braces");
  S *s = new S[2]();
  __CPROVER_assert(s[1].i == 0 && s[1].l == 0, "aggregate elements");
  int *c = new int[4]{1, 2};
  __CPROVER_assert(c[0] == 1 && c[1] == 2 && c[3] == 0, "list");
  C *d = new C[3]{5};
  __CPROVER_assert(d[0].v == 5 && d[1].v == 7 && d[2].v == 7, "class");
  __CPROVER_assert(c[2] == 3, "WRONG (must FAIL)");
}
