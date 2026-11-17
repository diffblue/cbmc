// Test that variadic template classes accept multiple arguments
template <typename... Ts>
struct holder
{
};

template <typename T>
struct wrapper
{
  typedef holder<T, int> type;
};

int main()
{
  wrapper<char>::type h;
  return 0;
}
