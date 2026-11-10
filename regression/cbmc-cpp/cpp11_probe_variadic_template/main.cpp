// N5008 [temp.variadic]: sizeof... of a function parameter pack.
extern "C" void __CPROVER_assert(bool, const char *);
template <class... T>
int count(T...)
{
  return sizeof...(T);
}
int main()
{
  __CPROVER_assert(count(1, 2.0, 'c') == 3, "sizeof... of a pack");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
