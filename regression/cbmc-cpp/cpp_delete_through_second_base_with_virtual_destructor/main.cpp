// N5008 [expr.delete]/3: deleting an object through a pointer to a base
// class with a virtual destructor is defined; [expr.delete]/6: the
// deallocation function is called with the address of the most derived
// object (the value returned by the allocation).
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
int main()
{
  Y *p = new Z;
  delete p;
  __CPROVER_assert(destroyed == 1, "through the second base");
  __CPROVER_assert(destroyed == 0, "WRONG (must FAIL)");
}
