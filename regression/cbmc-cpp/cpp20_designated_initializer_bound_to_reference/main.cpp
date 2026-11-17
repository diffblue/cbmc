// N5008 [dcl.init.list]/3.10, [over.ics.list]: a designated-initializer-list
// argument for a reference parameter initializes a temporary of the
// aggregate type, to which the reference binds:
// `v.push_back({.a = i, .b = 7})' calls push_back(S &&).
extern "C" void __CPROVER_assert(bool, const char *);
struct S
{
  unsigned a;
  unsigned long b;
};
struct V
{
  S s;
  int which = 0;
  void push_back(S &&x)
  {
    s = x;
    which = 2;
  }
  void push_back(const S &x)
  {
    s = x;
    which = 1;
  }
};
void by_const_ref(const S &x)
{
  __CPROVER_assert(x.a == 4 && x.b == 0, "const reference");
}
int main()
{
  V v;
  unsigned i = 3;
  v.push_back({.a = i, .b = 7});
  __CPROVER_assert(v.s.a == 3 && v.s.b == 7, "rvalue reference");
  __CPROVER_assert(v.which == 2, "S && overload");
  by_const_ref({.a = 4});
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
