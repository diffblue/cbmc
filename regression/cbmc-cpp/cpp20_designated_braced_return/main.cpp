// User-reported Issues 9 and 10.  N5008 [stmt.return]/2 + [dcl.init.list]:
// a braced return copy-list-initializes the result object; with a
// designated-initializer-list ([dcl.init.aggr]/3) or an empty list for a
// union ([dcl.init.list]/3.5, value-initialization) the conversion went to
// the positional member-wise path, which knew neither ("invalid implicit
// conversion from '<<type:>>'").
extern "C" void __CPROVER_assert(bool, const char *);
typedef unsigned long uint64_t;
struct In
{
  int x;
  int y;
};
struct S
{
  uint64_t a;
  int b;
  bool v;
  In in;
  int arr[2];
  int get() const
  {
    return b;
  }
};
union U
{
  int i;
  float f;
};
S make(unsigned i)
{
  return {.a = i, .b = 2, .v = true};
}
S make3(unsigned i)
{
  return {.a = i, .in = {.y = 9}, .arr = {1, 2}};
}
U make_u(bool ok)
{
  if(!ok)
    return {};
  return {.f = 1.5f};
}
int take(S s)
{
  return s.b;
}
int main()
{
  S s = make(5);
  __CPROVER_assert(
    s.a == 5 && s.b == 2 && s.v && s.in.x == 0 && s.arr[1] == 0,
    "designated braced return, rest value-initialised");
  S t = make3(6);
  __CPROVER_assert(
    t.a == 6 && t.b == 0 && !t.v && t.in.y == 9 && t.arr[1] == 2 &&
      t.get() == 0,
    "nested designators");
  __CPROVER_assert(make_u(false).i == 0, "return {} with a union return type");
  __CPROVER_assert(make_u(true).f == 1.5f, "union designated return");
  __CPROVER_assert(take({.b = 7}) == 7, "designated argument");
  return 0;
}
