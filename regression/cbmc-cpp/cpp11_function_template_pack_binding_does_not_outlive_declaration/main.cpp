extern "C" void __CPROVER_assert(bool, const char *);
template <class C, class... T>
auto call(C c, T... args) -> decltype(c(args...))
{
  return c(args...);
}
// N5008 [basic.scope.temp]/1: the template parameter pack `args' of this
// declaration is a different entity from the function parameter pack
// `args' above (in the MSVC STL, _Args names both kinds)
template <class... args>
void unrelated();
int twice(int x)
{
  return 2 * x;
}
int main()
{
  __CPROVER_assert(call(twice, 3) == 6, "one argument passed");
  __CPROVER_assert(call(twice, 3) == 3, "WRONG (must FAIL)");
  return 0;
}
