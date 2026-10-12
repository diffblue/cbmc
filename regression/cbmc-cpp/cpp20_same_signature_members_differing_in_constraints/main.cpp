// N5008 [basic.scope.scope]/4.4: two member declarations with the same
// parameter-type-list but different trailing requires-clauses are
// different functions; [over.match.viable]/3 removes the one whose
// constraints are not satisfied.  wrapper<int>'s copy uses the
// unconstrained copy constructor.  CBMC keeps a single symbol per
// signature (the first declaration's), finds it unsatisfied, and reports
// no match.
extern "C" void __CPROVER_assert(bool, const char *);

template <class T>
struct wrapper
{
  T value;
  wrapper(T v) : value(v)
  {
  }
  wrapper(const wrapper &other)
    requires(sizeof(T) > 100)
    : value(other.value + 1000)
  {
  }
  wrapper(const wrapper &other) : value(other.value + 1)
  {
  }
};

int main()
{
  wrapper<int> a{1};
  wrapper<int> b{a};
  __CPROVER_assert(b.value == 2, "unconstrained copy constructor");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
