// N5008 [dcl.fct.default]/1, [class.base.init]/13: a mem-initializer for a
// base whose constructor has default arguments passes them, and the base is
// constructed as a base subobject: it neither constructs the virtual base
// nor treats itself as the most derived object.  The shape of the MSVC
// STL's basic_istringstream, whose basic_istream base has the constructor
// `basic_istream(_Mysb *, bool _Isstd = false)' and initializes its virtual
// base basic_ios in the constructor body.
extern "C" void __CPROVER_assert(bool, const char *);

struct V
{
  int constructions = 0;
  int precision = 0;
  V()
  {
    ++constructions;
  }
  void init()
  {
    precision = 6;
  }
};

struct B : virtual V
{
  bool standard;
  explicit B(int *, bool is_standard = false) : standard(is_standard)
  {
    V::init();
  }
  virtual ~B()
  {
  }
};

struct D : B
{
  int buffer[8];
  D() : B(buffer)
  {
  }
};

int main()
{
  D d;
  __CPROVER_assert(d.constructions == 1, "virtual base constructed once");
  __CPROVER_assert(!d.standard, "default argument passed");
  __CPROVER_assert(d.precision == 6, "base body reaches the virtual base");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
