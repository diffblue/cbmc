// N5008 [over.match.list]/1 phase 1: `std::vector<E> a{E{2}}' selects the
// initializer-list constructor when each clause converts to E (a derived
// class's object does, [conv.ptr]).  The viability check skipped every
// clause that carried a type, assuming it was type-checked at the call site;
// a parsed `E{2}' carries one without being type-checked, so the
// initializer-list constructor looked non-viable and the iterator-pair
// template was tried with E (found no match for symbol 'vector').
// Regression guard for the call-site element type-check (round 185).
extern "C" void __CPROVER_assert(bool, const char *);
#include <vector>
struct E
{
  int v;
  E() : v(1)
  {
  }
  E(int x) : v(x)
  {
  }
};
struct D : E
{
  explicit D(int x) : E(x * 10)
  {
  }
};
int main()
{
  std::vector<E> a{D{2}}; // derived element: initializer_list<E>
  std::vector<E> b{E{3}, D{4}};
  __CPROVER_assert(a.size() == 1 && a[0].v == 20, "one derived element");
  __CPROVER_assert(b.size() == 2 && b[1].v == 40, "mixed");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
