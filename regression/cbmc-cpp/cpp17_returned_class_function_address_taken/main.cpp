extern "C" void __CPROVER_assert(bool, const char *);
struct V
{
  int k;
  V(int k) : k(k)
  {
  }
  V(const V &o) : k(o.k)
  {
  }
  ~V()
  {
  }
};
typedef V (*make_fn)(int);
static V make(int k);
// N5008 [conv.func]/1, [expr.call]/1: a call through a function pointer
// calls the function, whose class-type result initializes the result object
struct entry
{
  make_fn f;
  entry(make_fn f) : f(f)
  {
  }
};
static entry table[] = {entry{make}};
V make(int k)
{
  return V{k + 1};
}
int main()
{
  V v = table[0].f(4);
  __CPROVER_assert(v.k == 5, "call through function pointer");
  __CPROVER_assert(v.k == 4, "WRONG (must FAIL)");
  return 0;
}
