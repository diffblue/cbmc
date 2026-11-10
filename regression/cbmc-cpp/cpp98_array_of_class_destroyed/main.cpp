// N5008 [class.dtor]/13, [stmt.dcl]/2: when an array of class type goes out
// of scope its elements are destroyed, in the reverse order of their
// construction
extern "C" void __CPROVER_assert(bool, const char *);
int order[6];
int n = 0;
struct D
{
  int v;
  D() : v(0)
  {
  }
  D(int x) : v(x)
  {
  }
  ~D()
  {
    order[n++] = v;
  }
};
int main()
{
  {
    D a[2];
  }
  __CPROVER_assert(n == 2, "default-initialized array");
  {
    D b[2][2];
    b[0][0].v = 1;
    b[0][1].v = 2;
    b[1][0].v = 3;
    b[1][1].v = 4;
  }
  __CPROVER_assert(
    n == 6 && order[2] == 4 && order[3] == 3 && order[4] == 2 && order[5] == 1,
    "reverse order");
  __CPROVER_assert(order[2] == 1, "WRONG (must FAIL)");
}
