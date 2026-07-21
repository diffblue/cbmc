extern "C" void __CPROVER_assert(bool, const char *);

// N5008 [dcl.init.list]/3.7 + [class.mi]: direct-list-initialization
// of a class with a VIRTUAL base selects and calls its constructor,
// exactly like the parenthesized form -- `derived d(7)` converts fine.
// The braced form fails with "assignment error: 'd.@most_derived' not
// an lvalue": the braced constructor path emits the most-derived
// marker assignment against a non-lvalue.  The shape of
// `std::ofstream out{outfile}` (iostreams use virtual inheritance),
// which blocks dog-fooding src/goto-symex/solver_hardness.cpp.
// g++/clang++ accept and verify at runtime.

struct base
{
  int b;
};

struct derived : virtual base
{
  explicit derived(int v)
  {
    b = v;
  }
};

int main()
{
  derived d{7};
  __CPROVER_assert(d.b == 7, "virtual base member set");
  return 0;
}
