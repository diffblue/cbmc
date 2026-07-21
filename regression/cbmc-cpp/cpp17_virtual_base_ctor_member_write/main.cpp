extern "C" void __CPROVER_assert(bool, const char *);

// A constructor BODY (or mem-initializer) of a class with a VIRTUAL
// base writing its own member through `this` trips the pointer bounds
// check: "dereference failure: pointer outside object bounds in
// this->d".  The virtual-base this-adjustment/layout is modeled
// inconsistently with the write path.  Affects both `derived x{7}` and
// `derived x(7)` equally (pre-existing; exposed while fixing the
// braced-init lvalue issue, cpp17_virtual_base_braced_init).  The
// shape of std::ofstream construction (iostreams virtual inheritance),
// which still blocks dog-fooding solver_hardness.cpp.
// g++/clang++ accept and verify at runtime.

struct base
{
  int b;
};

struct derived : virtual base
{
  int d;
  explicit derived(int v) : d(v)
  {
  }
};

int main()
{
  derived x{7}; // braced: used to fail "'x.@most_derived' not an lvalue"
  x.b = 2;
  __CPROVER_assert(x.d == 7 && x.b == 2, "braced init with virtual base");
  return 0;
}
