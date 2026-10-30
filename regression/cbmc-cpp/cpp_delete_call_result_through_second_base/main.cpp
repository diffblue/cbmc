// N5008 [expr.delete]/6: the deallocation function is passed the address
// of the most derived object, also when the operand of delete is a call.
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
  delete make();
  __CPROVER_assert(destroyed == 1, "deleted through a call result");
  __CPROVER_assert(destroyed == 0, "WRONG (must FAIL)");
}
