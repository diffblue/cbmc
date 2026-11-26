// N5008 [class.base.init]/7: a braced-init-list mem-initializer
// list-initializes the member, so [over.match.list]/1 applies: with a viable
// initializer-list constructor the whole list is the single argument (phase
// 1).  The parser delivers the clauses of `ops{a, b}' as separate operands;
// for class-type elements no constructor of std::vector<E> matched them
// ("found no match for symbol 'vector'", the iterator-pair template was
// tried with E, E; CBMC's own and_exprt(std::vector<exprt>) shape).
extern "C" void __CPROVER_assert(bool, const char *);
#include <vector>
struct E
{
  int v;
};
struct And
{
  std::vector<E> ops;
  And(E a, E b) : ops{a, b}
  {
  }
};
struct Two
{
  std::vector<int> v;
  Two(int a, int b) : v{a, b}
  {
  }
};
int main()
{
  And x(E{1}, E{2});
  __CPROVER_assert(
    x.ops.size() == 2 && x.ops[1].v == 2,
    "braced mem-initializer, class elements");
  Two t(3, 4);
  __CPROVER_assert(
    t.v.size() == 2 && t.v[0] == 3, "braced mem-initializer, int elements");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
