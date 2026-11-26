// C++11 trailing return type with decltype in function template
template <typename T, typename U>
auto add(T a, U b) -> decltype(a + b)
{
  return a + b;
}
int main()
{
  auto r = add(1, 2);
  __CPROVER_assert(r == 3, "trailing decltype template");
  return 0;
}
