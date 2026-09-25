// N5008 [class.base.init]/9-10 with [dcl.init.aggr]/n and [dcl.init.list]: a
// non-static data member with a default member initializer that is a
// braced-init-list is initialized by that braced-init-list when no
// mem-initializer of a constructor names the member.  Here `pair stored{-1, 7}`
// must initialize `stored` by calling `pair(int, int)` with the list elements.
//
// CBMC previously default-constructed the member (ignoring the braced default
// member initializer), which failed for a class with no default constructor:
// "found no match for symbol 'pair'".  g++ and clang++ accept the program.
//
// assertion.2 must FAIL (non-vacuity).

extern "C" void __CPROVER_assert(int, const char *);

struct pair
{
  int a;
  int b;
  pair(int x, int y) : a(x), b(y)
  {
  }
};

struct Map
{
  pair stored{-1, 7}; // braced default member initializer, no default ctor
};

int main()
{
  Map m;
  __CPROVER_assert(
    m.stored.a == -1 && m.stored.b == 7,
    "braced default member initializer initializes class member");
  __CPROVER_assert(m.stored.a != -1, "WRONG must FAIL");
  return 0;
}
