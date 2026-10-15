// N5008 [over.match.list]/1.2 with [over.best.ics]/4.5: in `conj c{{1, 2,
// 3, 4}}' no initializer-list constructor exists, so the constructors of conj
// are candidates with the single argument {1, 2, 3, 4}.  For the copy and
// move constructors (first parameter: reference to conj) a user-defined
// conversion -- through conj(int, int, int, int) -- is not considered, so
// conj(vec) is the only viable candidate.  The front end also accepted the
// copy constructor and reported an ambiguity (CBMC's own
// instrument_spec_assigns.cpp, `and_exprt{{a, b, c, d}}' with and_exprt's
// four-operand and vector constructors, dog-fooding).
extern "C" void __CPROVER_assert(bool, const char *);
#include <initializer_list>
struct vec
{
  int n;
  vec(std::initializer_list<int> l) : n(int(l.size()))
  {
  }
};
struct conj
{
  int ops;
  conj(int, int, int, int) : ops(4)
  {
  }
  explicit conj(vec v) : ops(100 + v.n)
  {
  }
};
int main()
{
  // N5008 [over.best.ics]/4.5: for the copy constructor conj(const conj &)
  // the one-element list {{1, 2, 3, 4}} would need a user-defined conversion
  // to conj, which is not considered; conj(vec) is selected
  conj c{{1, 2, 3, 4}};
  __CPROVER_assert(c.ops == 104, "vector constructor");
  conj t = conj{{1, 2}};
  __CPROVER_assert(t.ops == 102, "functional form");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
