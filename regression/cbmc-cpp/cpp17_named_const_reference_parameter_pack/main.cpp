extern "C" void __CPROVER_assert(bool, const char *);
// N5008 [temp.variadic]/5, [dcl.init.ref]/5: the pattern `const T &' keeps
// its const for each element, so a prvalue argument binds to the
// expanded parameter
template <class... T>
int count(const T &...t)
{
  return sizeof...(t);
}
template <class... T>
long sum(const T &...t)
{
  return (0 + ... + t);
}
int main()
{
  int i = 4;
  __CPROVER_assert(
    count(i, 2) == 2 && count(1, 2.0, 'c') == 3 && sum(i, 2, 3L) == 9,
    "prvalues bind to const T &");
  __CPROVER_assert(sum(i, 2) == 5, "WRONG (must FAIL)");
  return 0;
}
