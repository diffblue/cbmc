extern "C" void __CPROVER_assert(bool, const char *);
struct base
{
  virtual int f()
  {
    return 1;
  }
};
struct derived : base
{
  int f() override
  {
    return 2;
  }
};
derived global;
base *make();
static base *p = make();
base *make()
{
  static derived local;
  return &local;
}
int main()
{
  base &b = global;
  __CPROVER_assert(b.f() == 2, "global");
  __CPROVER_assert(p->f() == 2, "static local");
  __CPROVER_assert(p->f() == 1, "WRONG (must FAIL)");
  return 0;
}
