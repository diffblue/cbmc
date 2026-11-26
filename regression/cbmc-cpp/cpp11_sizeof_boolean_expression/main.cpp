extern "C" void __CPROVER_assert(bool, const char *);
template <class T, class U>
struct same
{
  static const bool value = false;
};
template <class T>
struct same<T, T>
{
  static const bool value = true;
};
int main()
{
  // comparisons and the logical operators have type bool
  int x = 1;
  __CPROVER_assert(sizeof(x > 0) == sizeof(bool), "relational");
  __CPROVER_assert(sizeof(x == 0) == 1, "equality");
  __CPROVER_assert(sizeof(x && x) == 1 && sizeof(x || x) == 1, "logical");
  __CPROVER_assert(sizeof(!x) == 1, "not");
  __CPROVER_assert(same<decltype(x < 2), bool>::value, "decltype");
  auto b = x != 2;
  __CPROVER_assert(sizeof(b) == 1, "deduced");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
