extern "C" void __CPROVER_assert(bool, const char *);
template <bool B, class T = void>
struct enable_if
{
};
template <class T>
struct enable_if<true, T>
{
  typedef T type;
};
template <class T>
struct is_int
{
  static const bool value = false;
};
template <>
struct is_int<int>
{
  static const bool value = true;
};
template <class T, typename enable_if<is_int<T>::value, bool>::type = true>
int f()
{
  return 1;
}
template <class T, typename enable_if<!is_int<T>::value, bool>::type = false>
int f()
{
  return 2;
}
int main()
{
  __CPROVER_assert(f<int>() == 1, "first template");
  __CPROVER_assert(f<char>() == 2, "second template");
  __CPROVER_assert(f<char>() == 1, "WRONG (must FAIL)");
}
