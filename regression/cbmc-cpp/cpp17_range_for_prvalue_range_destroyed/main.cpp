// N5008 [stmt.ranged]/1, [class.temporary]/6, [dcl.init.general]/16.6.1:
// `auto &&__range = make(5)' binds to the call's result, which lives until
// the end of the loop and is then destroyed -- once
extern "C" void __CPROVER_assert(bool, const char *);
int destructions = 0;
struct D
{
  int *p;
  D(int x) : p(new int(x))
  {
  }
  D(const D &o) : p(new int(*o.p))
  {
  }
  ~D()
  {
    delete p;
    ++destructions;
  }
  int *begin()
  {
    return p;
  }
  int *end()
  {
    return p + 1;
  }
};
D make(int x)
{
  return D(x);
}
int main()
{
  int s = 0;
  for(int x : make(5))
  {
    __CPROVER_assert(destructions == 0, "alive in the loop");
    s += x;
  }
  for(int x : D(6))
    s += x;
  __CPROVER_assert(s == 11 && destructions == 2, "destroyed once each");
  __CPROVER_assert(destructions == 0, "WRONG (must FAIL)");
}
