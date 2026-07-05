// N5008 [dcl.fct]/[expr.type]: a function template with a trailing return type
// that nests a decltype inside a template-id -- e.g. util/range.h's
//   template <typename C> auto make_range(C &c) -> ranget<decltype(c.begin())>
// -- must have its parameter names in scope when the trailing return type (and
// the decltype it contains) is resolved during template argument deduction.
// CBMC only scoped the parameters when the return type *was* a decltype, not
// when a decltype was nested in a template argument, so this overload was
// wrongly removed from the candidate set ("found no match").  g++/clang accept.

extern "C" void __CPROVER_assert(int, const char *);

template <typename It>
struct R
{
  It b;
};

template <typename C>
auto mk(C &c) -> R<decltype(c.begin())>
{
  return R<decltype(c.begin())>{c.begin()};
}

struct Cont
{
  int *begin() { return 0; }
  int *end() { return 0; }
};

int main()
{
  Cont c;
  auto r = mk(c);
  __CPROVER_assert(r.b == 0, "trailing R<decltype(c.begin())> deduced");
  __CPROVER_assert(r.b != 0, "WRONG must FAIL");
  return 0;
}
