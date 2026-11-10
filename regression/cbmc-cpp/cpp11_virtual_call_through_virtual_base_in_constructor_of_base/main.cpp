// N5008 [class.cdtor]/4: during B's constructor, a call of V::g on the
// object reaches B::g, the final overrider in B; [class.virtual]/2: after
// construction, the call reaches D's final overrider, B::g.  D adds data
// members, so V lies at another offset from B than in a complete B.
extern "C" void __CPROVER_assert(bool, const char *);
struct V
{
  int v = 5;
  virtual int g() const
  {
    return v;
  }
  virtual ~V() = default;
};
int askg(const V &x)
{
  return x.g();
}
struct B : virtual V
{
  int b[4] = {1, 2, 3, 4};
  int seen;
  B()
  {
    seen = askg(*this);
  }
  int g() const override
  {
    return 30 + v + b[3];
  }
};
struct D : B
{
  int d[8];
};
int main()
{
  D d;
  __CPROVER_assert(d.seen == 39, "B under construction");
  __CPROVER_assert(askg(d) == 39, "after construction");
  __CPROVER_assert(d.seen == 5, "WRONG (must FAIL)");
}
