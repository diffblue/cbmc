extern "C" void __CPROVER_assert(bool, const char *);
struct partial
{
  int v;
};
struct strong
{
  int v;
};
auto pick()
{
  constexpr unsigned kinds[] = {1, 0};
  constexpr unsigned c = kinds[1];
  // the condition is a constant expression: only the selected branch
  // contributes to the deduced return type ([stmt.if]/2,
  // [dcl.spec.auto.general]/10)
  if constexpr(c == 0)
    return partial{1};
  else
    return strong{2};
}
template <class T>
auto pick_template()
{
  constexpr unsigned kinds[] = {sizeof(T)};
  if constexpr(kinds[0] == 1)
    return partial{3};
  else
    return strong{4};
}
int main()
{
  __CPROVER_assert(
    pick().v == 1, "local constexpr array element in if constexpr");
  __CPROVER_assert(pick_template<char>().v == 3, "in a template");
  __CPROVER_assert(pick_template<int>().v == 4, "the other branch");
  __CPROVER_assert(pick().v == 2, "WRONG (must FAIL)");
}
