// N5008 [temp.deduct]/[expr.type]: resolving a function template whose trailing
// return type contains a `decltype` naming a parameter (e.g.
// `template <class C> auto make_range(C &c) -> ranget<decltype(c.begin())>`)
// must not be affected by a previous, unrelated resolution of the same
// template.
//
// CBMC resolves such a return type by putting a synthetic symbol for the
// parameter into scope so `decltype(c.begin())` resolves; that symbol was keyed
// by the template scope + parameter name and never removed.  Speculatively
// matching the one-parameter container overload against a two-argument iterator
// call `make_range(begin, end)` deduced `c` from the first argument and left a
// stale symbol of the wrong type behind.  The subsequent, correct resolution of
// `make_range(container)` then found the symbol already present, skipped its own
// insertion, and evaluated `decltype(c.begin())` against the stale type --
// failing and removing the only viable overload ("found no match for
// make_range").  Fixed by refreshing the synthetic symbol's type on each
// resolution.
//
// Reduced (via cvise keeping real headers) from src/util/structured_data.cpp's
// `make_range(components).concat(make_range(begin, end))`.

extern "C" void __CPROVER_assert(int, const char *);

template <typename It>
struct ranget
{
  It b, e;
  ranget(It b, It e) : b(b), e(e) {}
  int count() const
  {
    int n = 0;
    for(It i = b; i != e; ++i)
      ++n;
    return n;
  }
  // A member function template taking another range (mirrors range.h::concat).
  template <typename OtherIt>
  int concat_count(ranget<OtherIt> other) const
  {
    return count() + other.count();
  }
};

// iterator overload
template <typename It>
ranget<It> make_range(It begin, It end)
{
  return {begin, end};
}

// container overload with a trailing return type using decltype
template <typename C>
auto make_range(C &c) -> ranget<decltype(c.begin())>
{
  return {c.begin(), c.end()};
}

struct vec
{
  int a[5];
  int *begin() { return a; }
  int *end() { return a + 5; }
};

int main()
{
  vec v;
  // receiver: container-form make_range (trailing-return decltype);
  // argument: iterator-form make_range.  This chain used to fail resolution.
  int total = make_range(v).concat_count(make_range(v.begin(), v.begin() + 2));
  __CPROVER_assert(total == 7, "5 + 2 == 7");
  __CPROVER_assert(total == 99, "WRONG: must fail");
  return 0;
}
