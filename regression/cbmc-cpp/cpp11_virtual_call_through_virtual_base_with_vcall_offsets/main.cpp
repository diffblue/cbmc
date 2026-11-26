// N5008 [class.cdtor]/4, [class.virtual]/2: V::g called on the object
// reaches B::g during B's construction, and M::g during M's construction
// and afterwards.  B and M lie at different offsets from V in a complete
// B, M and D (which adds data members), so the thunk that V's table enters
// the overrider through must read the offset from the table it was called
// through (Itanium C++ ABI 2.5.3 vcall offsets).
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
struct M : B
{
  int m[3] = {7, 8, 9};
  int seen_m;
  M()
  {
    seen_m = askg(*this);
  }
  int g() const override
  {
    return 50 + v + m[2];
  }
};
struct D : M
{
  int d[8];
};
int main()
{
  D d;
  __CPROVER_assert(d.seen == 39, "B under construction");
  __CPROVER_assert(d.seen_m == 64, "M under construction");
  __CPROVER_assert(askg(d) == 64, "after construction");
  __CPROVER_assert(d.seen == 5, "WRONG (must FAIL)");
}
