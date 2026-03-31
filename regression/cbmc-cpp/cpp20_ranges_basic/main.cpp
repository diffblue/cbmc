#if !defined(_MSC_VER) && __has_include(<ranges>)
// C++20 std::ranges basic usage
#  include <ranges>

int main()
{
  int arr[] = {1, 2, 3, 4, 5};
  int sum = 0;
  for(auto x : arr | std::views::take(3))
    sum += x;
  __CPROVER_assert(sum == 6, "ranges take");
  return 0;
}

#else
int main()
{
}
#endif
