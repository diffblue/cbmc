// N5008 [class.virtual]/8: D::self, returning D *, overrides B::self,
// returning B * (covariant return types).  `d.self()' calls D::self and
// `b.self()' through B & dispatches to it; both yield &d.
extern "C" void __CPROVER_assert(bool, const char *);
struct B
{
  virtual B *self()
  {
    return this;
  }
  virtual int id()
  {
    return 1;
  }
  virtual ~B() = default;
};
struct D : B
{
  D *self() override
  {
    return this;
  }
  int id() override
  {
    return 2;
  }
};
int main()
{
  D d;
  B &b = d;
  __CPROVER_assert(d.self() == &d, "direct call");
  __CPROVER_assert(b.self() == &d && b.self()->id() == 2, "virtual call");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
