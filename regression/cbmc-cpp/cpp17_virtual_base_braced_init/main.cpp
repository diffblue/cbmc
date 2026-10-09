extern "C" void __CPROVER_assert(bool, const char *);

// N5008 [dcl.init.list]/3.7 + [class.mi]: direct-list-initialization of
// a class with a VIRTUAL base selects and calls its constructor,
// exactly like the parenthesized form.  The braced form used to fail
// with "assignment error: 'x.@most_derived' not an lvalue": the object
// symbol built by convert_initializer for the braced route lacked the
// lvalue marking that cpp_constructor propagates to the @most_derived
// writes it synthesizes -- fixed 2026-07-21.  The residual virtual-base
// defect (constructor BODY writes through `this` fail the bounds
// check) is tracked in cpp17_virtual_base_ctor_member_write.
// g++/clang++ accept and verify at runtime.

struct base
{
  int b;
};

struct derived : virtual base
{
  int d;
  derived()
  {
  }
};

int main()
{
  derived x{}; // braced: used to fail "'x.@most_derived' not an lvalue"
  x.d = 7;
  x.b = 2;
  __CPROVER_assert(x.d == 7 && x.b == 2, "braced init with virtual base");
  return 0;
}
