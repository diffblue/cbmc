// N5008 [dcl.init.aggr]/4-5 (C++17 aggregates with bases): the base element
// is aggregate-initialized from its initializer; elements without one are
// initialized from their default member initializers or value-initialized
extern "C" void __CPROVER_assert(bool, const char *);
struct A
{
  int a;
  int c = 9;
};
struct E : A
{
  int e;
};
int main()
{
  E x{{1}, 2};
  __CPROVER_assert(x.a == 1 && x.c == 9 && x.e == 2, "braced base element");
  E y{};
  __CPROVER_assert(y.a == 0 && y.c == 9 && y.e == 0, "empty list");
  E z = {};
  __CPROVER_assert(z.a == 0 && z.c == 9 && z.e == 0, "copy-list");
  __CPROVER_assert(x.c == 0, "WRONG (must FAIL)");
}
