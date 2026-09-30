extern "C" void __CPROVER_assert(bool, const char *);
int destroyed = 0;
struct A
{
  int i = 0;
  virtual ~A()
  {
    ++destroyed;
  }
  virtual int id() const
  {
    return 1;
  }
};
struct B : A
{
};
struct C : A
{
  int id() const override
  {
    return 3;
  }
};
struct D : B, C
{
  ~D()
  {
    destroyed += 10;
  }
};
int main()
{
  // [class.dtor]/13 virtual destructor through either A subobject destroys
  // the complete D object ([expr.delete]/3); each A is destroyed once
  A *p = static_cast<C *>(new D);
  __CPROVER_assert(p->id() == 3, "C's overrider in C's A");
  A *q = static_cast<B *>(new D);
  __CPROVER_assert(q->id() == 1, "A's own in B's A");
  delete p;
  __CPROVER_assert(destroyed == 12, "D and both A subobjects destroyed");
  delete q;
  __CPROVER_assert(destroyed == 24, "again through the other path");
  __CPROVER_assert(destroyed == 13, "WRONG (must FAIL)");
}
