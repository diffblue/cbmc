#if !defined(_MSC_VER) && __has_include(<span>)
// C++20 std::span
#  include <span>
int main()
{
  int arr[] = {1, 2, 3, 4, 5};
  std::span<int> s(arr, 5);
  __CPROVER_assert(s.size() == 5, "span size");
  __CPROVER_assert(s[0] == 1, "span element");
}

#else
int main()
{
}
#endif
