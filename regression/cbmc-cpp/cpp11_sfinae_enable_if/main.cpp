// C++11 SFINAE with enable_if
template <bool B, typename T = void>
struct enable_if
{
};
template <typename T>
struct enable_if<true, T>
{
  typedef T type;
};
template <typename T>
typename enable_if<sizeof(T) <= 4, int>::type classify(T)
{
  return 0;
}
template <typename T>
typename enable_if<(sizeof(T) > 4), int>::type classify(T)
{
  return 1;
}
int main()
{
  __CPROVER_assert(classify(42) == 0, "int is small");
  __CPROVER_assert(classify(42LL) == 1, "long long is big");
  return 0;
}
