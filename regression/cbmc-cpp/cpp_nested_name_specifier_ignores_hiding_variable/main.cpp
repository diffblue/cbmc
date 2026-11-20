extern "C" void __CPROVER_assert(bool, const char *);
struct N
{
  static const int b = 2;
};
// [basic.lookup.qual.general]/1: N in N::b considers only namespaces, types
// and templates whose specializations are types, so it finds struct N, not
// the parameter N that hides it
int f(int N)
{
  return N + N::b;
}
int main()
{
  __CPROVER_assert(f(1) == 3, "class hidden by parameter");
  __CPROVER_assert(f(1) != 3, "WRONG (must FAIL)");
}
