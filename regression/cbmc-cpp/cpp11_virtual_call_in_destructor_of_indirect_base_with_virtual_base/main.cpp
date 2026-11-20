// N5008 [class.cdtor]/4: a virtual function called from a destructor on
// the object under destruction is the final overrider in the destructor's
// class.  A, destroyed as a base subobject of M, which is a base subobject
// of D, has a virtual base: while A's destructor runs, ask(*this) must
// call A::id.
extern "C" void __CPROVER_assert(bool, const char *);
int log_a = -1, log_m = -1;
struct V
{
  int data = 42;
  virtual int id() const
  {
    return 0;
  }
  virtual ~V() = default;
};
int ask(const V &v)
{
  return v.id() * 100 + v.data;
}
struct A : virtual V
{
  ~A()
  {
    log_a = ask(*this);
  }
  int id() const override
  {
    return 1;
  }
};
struct M : A
{
  ~M()
  {
    log_m = ask(*this);
  }
  int id() const override
  {
    return 2;
  }
};
struct D : M
{
  int id() const override
  {
    return 3;
  }
};
int main()
{
  {
    D d;
  }
  __CPROVER_assert(log_a == 142, "A under destruction");
  __CPROVER_assert(log_m == 242, "M under destruction");
  __CPROVER_assert(log_a == 342, "WRONG (must FAIL)");
}
