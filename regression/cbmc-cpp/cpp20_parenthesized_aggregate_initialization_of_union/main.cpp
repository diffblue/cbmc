// N5008 [dcl.init.general]/16.6.2.2 (C++20), [dcl.init.aggr]/2: a union
// is an aggregate whose elements are its non-static data members;
// `Rep(e)' with no viable constructor copy-initializes the first member
// from e.  libc++'s basic_string (Xcode 26) initializes its union member
// `__rep_(__short())' in every constructor.
extern "C" void __CPROVER_assert(bool, const char *);
struct Short
{
  unsigned char size;
  char data[7];
};
struct Long
{
  unsigned long cap;
};
union Rep
{
  Short s;
  Long l;
};
struct Str
{
  Rep rep;
  Str() : rep(Short())
  {
  }
  explicit Str(int) : rep(Short{3, {'a'}})
  {
  }
};
struct Pair
{
  int a;
  int b;
};
struct Holder
{
  Pair p;
  Holder() : p(1, 2)
  {
  }
};
int main()
{
  Str s;
  __CPROVER_assert(s.rep.s.size == 0, "union from first member's type");
  Str t(1);
  __CPROVER_assert(t.rep.s.size == 3 && t.rep.s.data[0] == 'a', "with value");
  Rep r(Short{4, {}});
  __CPROVER_assert(r.s.size == 4, "local union");
  Holder h;
  __CPROVER_assert(h.p.a == 1 && h.p.b == 2, "struct member");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
