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
template <class T>
struct S
{
  int k;
  template <
    class U = T,
    typename enable_if<is_int<U>::value, bool>::type = true>
  S() : k(1)
  {
  }
  template <
    class U = T,
    typename enable_if<!is_int<U>::value, bool>::type = false>
  explicit S() : k(2)
  {
  }
};
int main()
{
  S<int> a;
  S<char> b;
  __CPROVER_assert(a.k == 1, "first constructor template");
  __CPROVER_assert(b.k == 2, "second constructor template");
  __CPROVER_assert(b.k == 1, "WRONG (must FAIL)");
}
