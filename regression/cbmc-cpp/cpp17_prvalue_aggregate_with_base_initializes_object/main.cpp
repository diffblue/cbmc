// N5008 [dcl.init.aggr]/2, /4 (C++17: a class with a public base is an
// aggregate), [dcl.init.general]/16.6.1: `D t = D{{6}, 7};' initializes t
// directly from the prvalue, whose base E is initialized from {6} and whose
// member w from 7.
extern "C" void __CPROVER_assert(bool, const char *);

struct E
{
  int v;
};
struct D : E
{
  int w;
};
struct Empty
{
};
struct F
{
  int f;
};
struct M : Empty, E, F
{
  int m;
};

int main()
{
  D d{{6}, 7};
  __CPROVER_assert(d.v == 6 && d.w == 7, "direct-list-initialization");
  D t = D{{6}, 7};
  __CPROVER_assert(t.v == 6 && t.w == 7, "from the prvalue");
  M u = M{{}, {1}, {2}, 3};
  __CPROVER_assert(
    u.v == 1 && u.f == 2 && u.m == 3, "empty and non-empty bases");
  __CPROVER_assert(t.w == 0, "WRONG (must FAIL)");
  return 0;
}
