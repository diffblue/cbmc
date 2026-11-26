// N5008 [dcl.init.general]/16.6.1, [class.temporary]/2, [stmt.return]/2: a
// prvalue of the class type initializes the object directly; no temporary
// is materialized, copied and destroyed
extern "C" void __CPROVER_assert(bool, const char *);
int copies = 0;
int destructions = 0;
struct D
{
  int v;
  D(int x) : v(x)
  {
  }
  D(const D &o) : v(o.v)
  {
    ++copies;
  }
  ~D()
  {
    ++destructions;
  }
};
struct A
{
  D d;
};
D make(int x)
{
  return D(x);
}
int main()
{
  {
    D x = D(4);
    D y = make(5);
    A a{make(6)};
    D arr[2] = {D(1), D(2)};
    __CPROVER_assert(
      x.v + y.v + a.d.v + arr[1].v == 17 && copies == 0 && destructions == 0,
      "no copies");
  }
  __CPROVER_assert(destructions == 5, "each object destroyed once");
  __CPROVER_assert(copies == 1, "WRONG (must FAIL)");
}
