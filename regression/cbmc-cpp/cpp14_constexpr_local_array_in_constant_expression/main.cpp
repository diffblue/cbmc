extern "C" void __CPROVER_assert(bool, const char *);
typedef unsigned long size_t;
enum category : unsigned
{
  none,
  partial,
  weak,
  strong,
  count
};
constexpr category classify(int v)
{
  return v < 0 ? none : v == 0 ? partial : strong;
}
// libc++'s __compute_comp_type: a local array mutated during the evaluation
template <size_t N>
constexpr category compute(const category (&types)[N])
{
  int seen[count] = {};
  for(auto t : types)
    ++seen[t];
  if(seen[none])
    return none;
  if(seen[partial])
    return partial;
  return strong;
}
constexpr category global[] = {strong, partial};
static_assert(compute(global) == partial, "namespace-scope array");
int local()
{
  // a constexpr local array: its initializer is constant-evaluated (the
  // constexpr calls fold) and the array is usable in constant expressions
  constexpr category kinds[] = {strong, classify(3), classify(0)};
  constexpr category c = compute(kinds);
  static_assert(c == partial, "local constexpr array passed by reference");
  static_assert(kinds[1] == strong, "element read");
  return c;
}
int main()
{
  __CPROVER_assert(local() == partial, "the constant at run time");
  __CPROVER_assert(local() == strong, "WRONG (must FAIL)");
}
