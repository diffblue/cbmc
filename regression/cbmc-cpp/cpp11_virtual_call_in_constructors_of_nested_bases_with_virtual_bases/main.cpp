// N5008 [class.cdtor]/4: a virtual function called from a constructor on
// the object under construction is the final overrider in the
// constructor's class.  A, B and M are constructed as base subobjects of
// D (B as M's second base, after a dynamic base without virtual bases),
// with two virtual bases whose members the constructors read.
extern "C" void __CPROVER_assert(bool, const char *);
struct V
{
  int data = 42;
  virtual int id() const
  {
    return 0;
  }
  virtual ~V() = default;
};
struct W
{
  int w = 7;
  virtual int wid() const
  {
    return 10;
  }
  virtual ~W() = default;
};
int ask(const V &v)
{
  return v.id() * 100 + v.data;
}
int askw(const W &w)
{
  return w.wid() * 100 + w.w;
}
struct Pad
{
  int pad[3];
  virtual int p() const
  {
    return 5;
  }
  virtual ~Pad() = default;
};
struct A : virtual V, virtual W
{
  int seen, seenw;
  A()
  {
    seen = ask(*this);
    seenw = askw(*this);
  }
  int id() const override
  {
    return 1;
  }
  int wid() const override
  {
    return 11;
  }
};
struct B : A
{
  int seen_b;
  B()
  {
    seen_b = ask(*this);
  }
  int id() const override
  {
    return 2;
  }
};
struct M : Pad, B
{
  int seen_m;
  M()
  {
    seen_m = ask(*this);
  }
  int id() const override
  {
    return 3;
  }
};
struct D : M
{
  int id() const override
  {
    return 4;
  }
  int wid() const override
  {
    return 14;
  }
};
int main()
{
  D d;
  __CPROVER_assert(d.seen == 142, "A under construction");
  __CPROVER_assert(d.seenw == 1107, "A under construction, second base");
  __CPROVER_assert(d.seen_b == 242, "B under construction");
  __CPROVER_assert(d.seen_m == 342, "M under construction");
  __CPROVER_assert(ask(d) == 442 && askw(d) == 1407, "after construction");
  M m;
  __CPROVER_assert(
    m.seen == 142 && m.seen_b == 242 && m.seen_m == 342, "M complete");
  B b;
  __CPROVER_assert(b.seen == 142 && b.seen_b == 242, "B complete");
  __CPROVER_assert(d.seen == 442, "WRONG (must FAIL)");
}
