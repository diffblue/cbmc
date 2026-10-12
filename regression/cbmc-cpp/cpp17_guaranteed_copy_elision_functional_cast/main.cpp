// N5008 [dcl.init.general]/16.6.1, [expr.type.conv]/2: `T(e)' with a prvalue
// e of type T is e itself -- the object is initialized directly, without a
// copy or move constructor (C++17 guaranteed copy elision).  CBMC calls the
// move constructor (deleted here: "not accessible") or the copy constructor.
extern "C" void __CPROVER_assert(bool, const char *);

struct Count
{
  static int copies;
  int x;
  Count(int v) : x(v)
  {
  }
  Count(const Count &o) : x(o.x)
  {
    ++copies;
  }
};
int Count::copies = 0;

struct NM
{
  int x;
  NM(int v) : x(v)
  {
  }
  NM(const NM &) = delete;
  NM(NM &&) = delete;
};
NM make(int v)
{
  return NM{v};
}

int main()
{
  Count d = Count(Count(6));
  __CPROVER_assert(d.x == 6 && Count::copies == 0, "no copy");
  NM b = NM(make(4));
  __CPROVER_assert(b.x == 4, "non-movable prvalue");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
