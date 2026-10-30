// N5008 [class.temporary]/6: a temporary bound to a reference persists
// for the lifetime of the reference and is then destroyed; a temporary
// bound to a reference parameter of a call is destroyed at the end of the
// full-expression (/6.10)
extern "C" void __CPROVER_assert(bool, const char *);
int destroyed = 0;
struct D
{
  int v;
  D(int x) : v(x)
  {
  }
  ~D()
  {
    ++destroyed;
  }
};
D make()
{
  return D(4);
}
const D &id(const D &d)
{
  return d;
}
int main()
{
  {
    const D &r = D(3);
    __CPROVER_assert(destroyed == 0 && r.v == 3, "alive while bound");
  }
  __CPROVER_assert(destroyed == 1, "destroyed with the reference");
  {
    D &&q = make();
    const int &m = D(5).v;
    __CPROVER_assert(destroyed == 1 && q.v + m == 9, "call result, member");
  }
  __CPROVER_assert(destroyed == 3, "both destroyed");
  {
    const D &a = id(D(6));
    __CPROVER_assert(destroyed == 4, "argument destroyed at once");
  }
  __CPROVER_assert(destroyed == 3, "WRONG (must FAIL)");
}
