extern "C" void __CPROVER_assert(bool, const char *);
struct plain
{
  int v;
};
struct no_copy
{
  no_copy &operator=(const no_copy &) = delete;
};
struct from_int
{
  from_int &operator=(int)
  {
    return *this;
  }
};
// N5008 [meta.unary.prop]: is_assignable<T, U> holds iff
// `declval<T>() = declval<U>()' is well-formed; for a class T that calls
// T's operator=, so a deleted one makes it false
int main()
{
  __CPROVER_assert(
    __is_assignable(plain &, const plain &) &&
      !__is_assignable(const plain &, const plain &) &&
      !__is_assignable(no_copy &, const no_copy &) &&
      __is_assignable(from_int &, int) && !__is_assignable(plain &, int),
    "operator= decides");
  __CPROVER_assert(
    __is_assignable(no_copy &, const no_copy &), "WRONG (must FAIL)");
  return 0;
}
