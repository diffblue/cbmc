// N5008 [expr.prim.lambda.closure]/1, [temp.spec.general]/1: a
// lambda-expression in a template has a distinct closure type in each
// specialization
extern "C" void __CPROVER_assert(bool, const char *);
template <class C>
int size_of()
{
  auto l = [] { return int(sizeof(C)); };
  return l();
}
template <class C>
struct S
{
  int f()
  {
    auto l = [] { return int(sizeof(C)); };
    return l();
  }
};
int main()
{
  __CPROVER_assert(
    size_of<char>() == 1 && size_of<long>() == 8, "function template");
  __CPROVER_assert(
    S<char>().f() == 1 && S<long>().f() == 8, "member of a class template");
  __CPROVER_assert(size_of<long>() == 1, "WRONG (must FAIL)");
}
