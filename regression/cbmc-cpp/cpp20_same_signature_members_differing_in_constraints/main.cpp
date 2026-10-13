// N5008 [basic.scope.scope]/4.4: two member declarations with the same
// parameter-type-list but different trailing requires-clauses declare
// different functions.  [over.match.viable]/3 removes a candidate whose
// constraints are not satisfied; of two satisfied ones,
// [over.match.best]/2.6 prefers the more constrained ([temp.constr.order]).
// The return types may differ: libc++'s transform_view has `__sentinel
// end()' and `__iterator end() requires common_range<_View>'.  CBMC kept
// one symbol per signature, the first declaration's.
extern "C" void __CPROVER_assert(bool, const char *);

template <class T>
concept small = sizeof(T) <= 4;

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

  long end() const
  {
    return 1;
  }
  int end() const
    requires small<T>
  {
    return 2;
  }
};

int main()
{
  wrapper<int> a{1};
  wrapper<int> b{a};
  __CPROVER_assert(b.value == 2, "unconstrained copy constructor");
  __CPROVER_assert(a.end() == 2, "more constrained, other return type");
  wrapper<long long> c{1};
  __CPROVER_assert(c.end() == 1, "unsatisfied twin");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
