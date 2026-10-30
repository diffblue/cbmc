// N5008 [class.base.init]/6-7: a delegating constructor's target
// initializes the complete class object, so it constructs the virtual bases
// exactly when the delegating constructor would have ([class.base.init]/13.1:
// only for the constructor of the most derived class).  The MSVC STL's
// basic_ofstream(const string &) delegates to basic_ofstream(const char *),
// whose class has the virtual base basic_ios.
extern "C" void __CPROVER_assert(bool, const char *);

int constructions = 0;

struct V
{
  int state;
  V() : state(1)
  {
    ++constructions;
  }
  void set(int s)
  {
    state = s;
  }
};

struct B : virtual V
{
  explicit B(int s)
  {
    set(s);
  }
  B() : B(7)
  {
  }
};

struct D : B
{
  D() : V(), B()
  {
  }
};

int main()
{
  B b;
  __CPROVER_assert(constructions == 1, "complete object: V constructed once");
  __CPROVER_assert(b.state == 7, "complete object: target ran");

  D d;
  __CPROVER_assert(constructions == 2, "base subobject: one more V");
  __CPROVER_assert(d.state == 7, "base subobject: target ran");

  __CPROVER_assert(b.state == 1, "WRONG (must FAIL)");
  return 0;
}
