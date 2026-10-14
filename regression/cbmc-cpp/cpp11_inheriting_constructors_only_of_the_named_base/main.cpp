// N5008 [namespace.udecl]/3, [class.inhctor.init]: `using base::base;'
// inherits the constructors OF base -- not those of base's own bases.  The
// front end also took propt's constructors, which base's component list
// holds as inherited members, and made `derived(const propt &)' and
// `derived(handler &)' (from propt) constructors initializing base from a
// propt: "found no match for symbol 'base'" for any class with a base
// that has a base (CBMC's own satcheck_minisat_no_simplifiert, six files
// of src/goto-checker and src/cprover, dog-fooding).
extern "C" void __CPROVER_assert(bool, const char *);
struct handler
{
  int verbosity = 1;
};
struct propt
{
  explicit propt(handler &h) : h(h)
  {
  }
  handler &h;
};
template <class T>
struct base : propt
{
  explicit base(handler &h) : propt(h), v(2)
  {
  }
  T v;
};
struct derived : base<int>
{
  using base<int>::base;
};
int main()
{
  handler h;
  derived s(h);
  derived t(s); // implicit copy constructor
  __CPROVER_assert(
    t.v == 2 && &t.h == &h, "copy of a class with inherited constructors");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
