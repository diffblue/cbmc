#if !defined(_MSC_VER) && __has_include(<span>)
#  include <span>

int main()
{
  int arr[] = {10, 20, 30};
  std::span<int> s(arr, 3);
  __CPROVER_assert(s.size() == 3, "size");
  __CPROVER_assert(s[0] == 10, "first");
  return 0;
}

#else
int main()
{
}
#endif
