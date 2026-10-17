// N5008 [over.match.list], [over.ics.list], [over.ics.rank]: when a class is
// list-initialized from a braced-init-list, overload resolution over its
// constructors must rank the candidates by the quality of the element
// conversion sequences.  A constructor taking the element(s) directly (here
// `vec(int)` for `{7}`) is preferred over a copy/move constructor, whose
// parameter (`const vec&` / `vec&&`) would require first materializing a `vec`
// from the list -- a user-defined conversion, which [over.best.ics] ranks
// below the direct list-initialization sequence.
//
// Here a base-class mem-initializer `Base(0, {7})` selects between
// `Base(int, src)` and `Base(int, vec)`.  `src` is an empty class, so `{7}` is
// not viable for it; `{7}` initializes `vec` via `vec(int)`.  g++ and clang++
// unambiguously pick `Base(int, vec)`.  CBMC instead reports
//   symbol 'vec' does not uniquely resolve
// -- resolving `vec` from `{7}` treats both `vec(int)` and the implicit copy
// constructor as equally viable and gives up.  Root of the "symbol 'codet'
// does not uniquely resolve" dog-food noise (std_code.h), where
// `codet(ID_assume, {std::move(expr)})` must pick the
// `codet(irep_idt, std::vector<exprt>)` constructor.
//
// assertion.2 must FAIL (non-vacuity).

extern "C" void __CPROVER_assert(int, const char *);

struct src
{
};

struct vec
{
  int v;
  vec(int x) : v(x)
  {
  }
};

int g_choice = 0;

struct Base
{
  Base(int, src)
  {
    g_choice = 1;
  }
  Base(int, vec)
  {
    g_choice = 2;
  }
};

struct Derived : Base
{
  Derived() : Base(0, {7})
  {
  }
};

int main()
{
  Derived d;
  __CPROVER_assert(
    g_choice == 2, "braced base-ctor arg selects the vec-taking overload");
  __CPROVER_assert(g_choice != 2, "WRONG must FAIL");
  return 0;
}
