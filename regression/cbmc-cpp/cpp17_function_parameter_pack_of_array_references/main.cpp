// N5008 [temp.deduct.call]/1, [temp.variadic]/5: in `const char
// (&...s)[N]' the function parameter pack's pattern names the NON-type
// pack N, deduced from each argument's array bound; g("ab", "c") has
// N = {3, 2}.  Deduction recorded the argument types as the elements of a
// type pack, and the pack expanded to a single parameter.
extern "C" void __CPROVER_assert(bool, const char *);
template <unsigned long... N>
int g(const char (&...s)[N])
{
  return (0 + ... + (int)N);
}
int main()
{
  __CPROVER_assert(g("ab", "c") == 5, "two");
  __CPROVER_assert(g() == 0, "empty");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
