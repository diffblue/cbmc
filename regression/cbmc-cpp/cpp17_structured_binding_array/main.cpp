// C++17 structured bindings with array
int main()
{
  int arr[3] = {1, 2, 3};
  auto [a, b, c] = arr;
  __CPROVER_assert(a == 1, "sb array a");
  __CPROVER_assert(c == 3, "sb array c");
  return 0;
}
