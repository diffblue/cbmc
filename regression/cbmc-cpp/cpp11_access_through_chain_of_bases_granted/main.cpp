// N5008 [class.access.base]/5.4 with /4.4: m, named in F, is accessible in
// G: E is a public base of F, D a public base of E, and m is a private member
// of D (A is a private base of D), accessible to D's friend G.  And in a
// member of D itself, through an object of the derived F.
extern "C" void __CPROVER_assert(bool, const char *);
struct A
{
protected:
  int m = 1;
};
struct D : private A
{
  friend struct G;
  static int peek(struct F &f);
};
struct E : D
{
};
struct F : E
{
};
int D::peek(F &f)
{
  return f.m;
}
struct G
{
  int get(F &f)
  {
    return f.m;
  }
};
int main()
{
  F f;
  G g;
  __CPROVER_assert(g.get(f) == 1, "friend of D, two levels down");
  __CPROVER_assert(D::peek(f) == 1, "member of D");
  __CPROVER_assert(g.get(f) == 2, "WRONG (must FAIL)");
  return 0;
}
