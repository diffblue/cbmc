// C++17 structured bindings with struct and array
struct Point
{
  int x;
  int y;
};
int main()
{
  Point p{3, 4};
  auto [a, b] = p;
  __CPROVER_assert(a == 3, "sb struct x");
  __CPROVER_assert(b == 4, "sb struct y");

  int arr[3] = {10, 20, 30};
  auto [u, v, w] = arr;
  __CPROVER_assert(u == 10, "sb array 0");
  __CPROVER_assert(w == 30, "sb array 2");
  return 0;
}
