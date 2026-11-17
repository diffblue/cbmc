// N5008 [stmt.pre]/4: a condition that is a structured binding declaration
// has the bound object, contextually converted to bool, as its decision
// variable; the bindings are in scope in both substatements
// ([stmt.pre]/2, [stmt.if]).
extern "C" void __CPROVER_assert(bool, const char *);
struct P
{
  int a, b;
  explicit operator bool() const
  {
    return a != 0;
  }
};
int main()
{
  int r = 0;
  if(auto [x, y] = P{0, 7})
    r = 1;
  else
    r = x + y;
  P p{4, 5};
  int s = 0;
  if(auto &[u, v] = p)
  {
    u = 10;
    s = u + v;
  }
  __CPROVER_assert(r == 7 && s == 15 && p.a == 10, "decision and bindings");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
