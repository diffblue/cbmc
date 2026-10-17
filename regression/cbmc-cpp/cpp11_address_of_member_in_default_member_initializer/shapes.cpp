extern "C" void __CPROVER_assert(bool, const char *);
struct s
{
  int x = 5;
  int *p = &x;
  int y = x + 1;
  // [expr.unary.op]/4: a parenthesized qualified-id names the member object
  int *pp = &(s::x);
  bool f()
  {
    // a qualified-id forms a pointer to member, also where `this' exists
    int s::*m = &s::y;
    (void)m;
    int *q = &x;
    return q == &x;
  }
};
struct t
{
  int a = 1;
  int *q = &a;
  t()
  {
  }
};
int main()
{
  s v;
  t w;
  __CPROVER_assert(
    v.p == &v.x && v.y == 6 && v.pp == &v.x && w.q == &w.a && v.f(),
    "member names in default member initializers");
  __CPROVER_assert(v.y == 5, "WRONG (must FAIL)");
}
