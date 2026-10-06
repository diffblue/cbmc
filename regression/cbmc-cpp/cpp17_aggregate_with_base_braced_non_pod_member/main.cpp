// N5008 [dcl.init.aggr]/4-5: the elements of an aggregate with a base are
// the base and the members; a braced list for a member that is itself an
// aggregate with a non-POD member aggregate-initializes that member
extern "C" void __CPROVER_assert(bool, const char *);
struct owner
{
  int *p;
  owner(int v) : p(new int(v))
  {
  }
  owner(const owner &o) : p(new int(*o.p))
  {
  }
  ~owner()
  {
    delete p;
  }
};
struct P
{
  int x, y;
};
struct A
{
  owner o;
  int k;
  P p;
};
struct C
{
  int s;
  C(int a, int b) : s(a + b)
  {
  }
};
struct E
{
};
struct B : E
{
  A a;
  C c;
};
int main()
{
  B b{{}, {owner(7), 3, {4, 5}}, {1, 2}};
  __CPROVER_assert(*b.a.o.p == 7 && b.a.k == 3, "member through the base path");
  __CPROVER_assert(b.a.p.y == 5 && b.c.s == 3, "nested list, constructor");
  __CPROVER_assert(b.a.k == 0, "WRONG (must FAIL)");
}
