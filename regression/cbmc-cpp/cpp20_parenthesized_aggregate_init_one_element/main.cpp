// N5008 [dcl.init.general]/16.6.2.2 (P0960): `T x(e)' with T an aggregate
// and no viable constructor initializes the first element from e and
// value-initializes the others
extern "C" void __CPROVER_assert(bool, const char *);
struct point
{
  int x;
  int y;
};
template <int I, class H>
struct leaf
{
  H value;
};
struct wrap
{
  point p;
};
int main()
{
  point a(4);
  __CPROVER_assert(a.x == 4 && a.y == 0, "first element");
  leaf<0, long> b(5);
  __CPROVER_assert(b.value == 5, "class template specialization");
  point c(a);
  __CPROVER_assert(c.x == 4, "copy constructor still preferred");
  wrap w(a);
  __CPROVER_assert(w.p.x == 4, "element of class type");
  __CPROVER_assert(a.x == 5, "WRONG (must FAIL)");
}
