extern "C" void __CPROVER_assert(bool, const char *);
// [temp.spec.partial.match]/1, [temp.constr.decl]: a constrained partial
// specialization of a primary template with a defaulted parameter is
// matched against the completed argument list impl<int, long long, 1>
template <typename, typename, int = 1>
struct impl
{
  using type = char;
};
template <typename T1, typename T2>
requires(sizeof(T1) > 0) struct impl<T1, T2>
{
  using type = T2;
};
template <typename T1, typename T2>
requires(sizeof(T1) > 99) struct impl<T1 *, T2>
{
  using type = T1;
};
int main()
{
  __CPROVER_assert(sizeof(impl<int, long long>::type) == 8, "satisfied");
  __CPROVER_assert(sizeof(impl<int *, long long>::type) == 8, "unsatisfied");
  __CPROVER_assert(sizeof(impl<int, long long, 2>::type) == 1, "primary");
  __CPROVER_assert(
    sizeof(impl<int, long long>::type) != 8, "WRONG (must FAIL)");
}
