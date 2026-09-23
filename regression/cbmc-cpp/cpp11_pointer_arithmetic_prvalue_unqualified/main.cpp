// N5008 [expr.type]/2, [expr.add]: the type of a pointer-arithmetic prvalue.
extern "C" void __CPROVER_assert(bool, const char *);

template <class T>
T &&declval();

int main()
{
  static_assert(
    __is_same(decltype(declval<int *const>() + declval<const long>()), int *),
    "const pointer xvalue + const long");
  static_assert(
    __is_same(decltype(declval<const int *const &>() + 1), const int *),
    "pointee const stays, pointer const goes");
  static_assert(
    __is_same(decltype(declval<int *const &>() - 1), int *), "minus");
  static_assert(
    __is_same(decltype(1 + declval<int *const &>()), int *), "int + pointer");
  static_assert(
    __is_same(decltype(declval<const int &>() + declval<const int &>()), int),
    "const int + const int");
  int a[3] = {1, 2, 3};
  int *const p = a;
  __CPROVER_assert(*(p + 2) == 3, "value");
  return 0;
}
