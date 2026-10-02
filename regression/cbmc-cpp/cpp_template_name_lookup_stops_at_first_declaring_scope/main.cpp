extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
struct f
{
  int v = 1;
  f(T)
  {
  }
};
namespace n
{
// [basic.lookup.general]/1, [basic.lookup.unqual]/1-2: lookup of f from g
// stops at namespace n, where it finds the function template n::f; the
// class template ::f is hidden
template <class T>
int f(T)
{
  return 2;
}
int g()
{
  return f<int>(0);
}
} // namespace n
int main()
{
  __CPROVER_assert(n::g() == 2, "namespace member hides global");
  __CPROVER_assert(n::g() != 2, "WRONG (must FAIL)");
}
