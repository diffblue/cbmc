// C++11 SFINAE with enable_if in return type
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
struct is_integral
{
  static constexpr bool value = false;
};
template <>
struct is_integral<int>
{
  static constexpr bool value = true;
};

template <typename T>
typename enable_if<is_integral<T>::value, int>::type classify(T)
{
  return 1;
}

template <typename T>
typename enable_if<!is_integral<T>::value, int>::type classify(T)
{
  return 2;
}

int main()
{
  __CPROVER_assert(classify(42) == 1, "integral");
  __CPROVER_assert(classify(3.14) == 2, "non-integral");
  return 0;
}
