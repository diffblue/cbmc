// N5008 [dcl.init.general]/16.6.3 + [over.match.copy]: initialising a class T
// from an object of a different class S considers S's conversion functions
// yielding T and T's converting constructors whose parameter takes S WITHOUT
// a further user-defined conversion ([over.best.ics.general]/4).  With every
// constructor of vector free to convert the argument through the conversion
// function TEMPLATE `operator C()' (C = size_type, vector &&,
// initializer_list), `std::vector<int> v = range;' was reported ambiguous
// ("symbol 'vector' does not uniquely resolve") -- the shape of
// util/range.h's ranget::operator containert().
extern "C" void __CPROVER_assert(bool, const char *);
#include <vector>

struct R
{
  const int *b;
  const int *e;
  template <typename C>
  C collect() const
  {
    return C(b, e);
  }
  template <typename C>
  operator C() const
  {
    return collect<C>();
  }
};
R make(const int *b, const int *e)
{
  return R{b, e};
}
std::vector<int> f(const int *b, const int *e)
{
  return make(b, e); // prvalue operand
}
std::vector<int> g(const R &r)
{
  return r; // lvalue operand
}
int main()
{
  int a[3] = {1, 2, 3};
  std::vector<int> v = f(a, a + 3);
  __CPROVER_assert(v.size() == 3 && v[2] == 3, "return of a prvalue");
  std::vector<int> w = g(make(a, a + 2));
  __CPROVER_assert(w.size() == 2, "return of an lvalue");
  std::vector<int> x = make(a, a + 1);
  __CPROVER_assert(x.size() == 1, "copy-initialization");
  std::vector<int> y(make(a, a + 3));
  __CPROVER_assert(
    y.size() == 3, "direct-initialization (g++/clang: CWG 2327)");
  return 0;
}
