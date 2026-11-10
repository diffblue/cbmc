extern "C" void __CPROVER_assert(bool, const char *);
// N5008 [class.virtual]: the virtual functions of a class that is never
// constructed cannot be called; 100 such classes with three virtual
// functions each need not occupy any of the 256 objects --object-bits 8
// allows
#define UNUSED_CLASS(n)                                                        \
  struct unused##n                                                             \
  {                                                                            \
    virtual int f()                                                            \
    {                                                                          \
      return n;                                                                \
    }                                                                          \
    virtual int g()                                                            \
    {                                                                          \
      return -n;                                                               \
    }                                                                          \
    virtual ~unused##n()                                                       \
    {                                                                          \
    }                                                                          \
  };
#define TEN(d)                                                                 \
  UNUSED_CLASS(d##0)                                                           \
  UNUSED_CLASS(d##1)                                                           \
  UNUSED_CLASS(d##2)                                                           \
  UNUSED_CLASS(d##3)                                                           \
  UNUSED_CLASS(d##4)                                                           \
  UNUSED_CLASS(d##5)                                                           \
  UNUSED_CLASS(d##6)                                                           \
  UNUSED_CLASS(d##7)                                                           \
  UNUSED_CLASS(d##8)                                                           \
  UNUSED_CLASS(d##9)
TEN(1)
TEN(2)
TEN(3)
TEN(4)
TEN(5)
TEN(6)
TEN(7)
TEN(8)
TEN(9)
TEN(10)
struct base
{
  virtual int f()
  {
    return 1;
  }
  virtual ~base()
  {
  }
};
struct derived : base
{
  int f() override
  {
    return 2;
  }
};
int main()
{
  derived d;
  base &b = d;
  __CPROVER_assert(b.f() == 2, "virtual call");
  __CPROVER_assert(b.f() == 1, "WRONG (must FAIL)");
  return 0;
}
