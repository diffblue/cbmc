// N5008 [class.access.general]/7: the definition of a static data
// member of a class outside its class-specifier has the access of a
// member -- it may use the class's private constructors.
// (The exact shape of goto_trace.h's trace_optionst::default_options.)
//
// The front end used to judge the constructor call in the
// out-of-class static member definition from namespace scope and
// reject it ("member 'S::S(this)' is not accessible"); it now
// re-enters the member's class scope around the initializer.
//
// g++/clang++ verify at runtime.
extern "C" void __CPROVER_assert(bool, const char *);

struct S
{
  int v;
  static const S def;
  explicit S(int x) : v(x)
  {
  }

private:
  S() : v(7)
  {
  }
};

const S S::def = S();

int main()
{
  __CPROVER_assert(S::def.v == 7, "static member built by private ctor");
  return 0;
}
