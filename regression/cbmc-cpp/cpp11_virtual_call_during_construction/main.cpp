// N5008 [class.cdtor]/4: a virtual call during construction/destruction of
// a base subobject dispatches to the overrider of the class being
// constructed, not of the most derived class.
extern "C" void __CPROVER_assert(bool, const char *);
int log_[8], n;
struct B
{
  virtual int f()
  {
    return 1;
  }
  B()
  {
    log_[n++] = f();
  }
  virtual ~B()
  {
    log_[n++] = f();
  }
};
struct D : B
{
  int f() override
  {
    return 2;
  }
  D()
  {
    log_[n++] = f();
  }
  ~D() override
  {
    log_[n++] = f();
  }
};
struct V
{
  virtual int g()
  {
    return 10;
  }
  V()
  {
  }
  virtual ~V()
  {
  }
};
struct M : virtual V
{
  int g() override
  {
    return 20;
  }
  M()
  {
    log_[n++] = g();
  }
  ~M() override
  {
    log_[n++] = g();
  }
};
struct E : M
{
  int g() override
  {
    return 30;
  }
  E()
  {
    log_[n++] = g();
  }
  ~E() override
  {
    log_[n++] = g();
  }
};
int main()
{
  {
    D d;
  }
  __CPROVER_assert(n == 4, "four calls");
  __CPROVER_assert(
    log_[0] == 1 && log_[1] == 2, "construction: B sees B::f, D sees D::f");
  __CPROVER_assert(
    log_[2] == 2 && log_[3] == 1, "destruction: D sees D::f, B sees B::f");
  n = 0;
  {
    E e;
  }
  __CPROVER_assert(
    log_[0] == 20 && log_[1] == 30 && log_[2] == 30 && log_[3] == 20,
    "with a virtual base");
  return 0;
}
