// N5008 [expr.delete]/6: the deallocation function is passed the address
// of the most derived object, also when the operand of delete is a call
// or has other side effects (evaluated once).
extern "C" void __CPROVER_assert(bool, const char *);
int destroyed = 0;
struct X
{
  int x;
  virtual ~X() = default;
};
struct Y
{
  int y;
  virtual ~Y() = default;
};
struct Z : X, Y
{
  ~Z()
  {
    ++destroyed;
  }
};
Y *make()
{
  return new Z;
}
int main()
{
  Y *ps[2] = {new Z, new Z};
  int i = 0;
  delete ps[i++];
  delete ps[i++];
  delete make();
  __CPROVER_assert(destroyed == 3 && i == 2, "deleted through a call result");
  __CPROVER_assert(destroyed == 2, "WRONG (must FAIL)");
}
