// Phase 3.2: Compound requirements
// requires(T x) { { expr } -> concept<args>; }
// Checks that expr is valid AND its type satisfies the concept.

template <class T, class U>
concept same_as = __is_same(T, U);

template <class T>
concept HasIntSize = requires(T c)
{
  {
    c.size()
    } -> same_as<int>;
};

// This should NOT satisfy HasIntSize (size() returns unsigned long)
struct WrongReturn
{
  unsigned long size() const
  {
    return 0;
  }
};

// Without compound requirement evaluation, CBMC skips the
// return type check and accepts WrongReturn as HasIntSize.
template <class T>
int check(T)
{
  return 0;
}

template <HasIntSize T>
int check(T)
{
  return 1;
}

int main()
{
  WrongReturn w;
  // With proper compound requirement evaluation, check(w) should
  // return 0 (WrongReturn doesn't satisfy HasIntSize because
  // size() returns unsigned long, not int).
  // Without it, CBMC skips the constraint and returns 1.
  __CPROVER_assert(check(w) == 0, "WrongReturn fails HasIntSize");
}
