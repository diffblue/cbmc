// N5008 [class.cdtor]/4: a virtual function called, directly or indirectly,
// from a constructor on the object under construction is the final overrider
// in the constructor's class.  A, constructed as a base subobject of M,
// which is a base subobject of D, has a virtual base: while A's constructor
// runs, ask(*this) must call A::id.
extern "C" void __CPROVER_assert(bool, const char *);
struct V
{
  virtual int id() const
  {
    return 0;
  }
  virtual ~V() = default;
};
int ask(const V &v)
{
  return v.id();
}
struct A : virtual V
{
  int seen;
  A()
  {
    seen = ask(*this);
  }
  int id() const override
  {
    return 1;
  }
};
struct M : A
{
  int seen_m;
  M()
  {
    seen_m = ask(*this);
  }
  int id() const override
  {
    return 2;
  }
};
struct D : M
{
  int id() const override
  {
    return 3;
  }
};
int main()
{
  D d;
  __CPROVER_assert(d.seen == 1, "A under construction");
  __CPROVER_assert(d.seen_m == 2, "M under construction");
  __CPROVER_assert(d.id() == 3, "after construction");
  __CPROVER_assert(d.seen == 3, "WRONG (must FAIL)");
}
