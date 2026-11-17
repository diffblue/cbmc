// C++11 uniform initialization
struct Point
{
  int x, y;
};
int main()
{
  Point p{10, 20};
  __CPROVER_assert(p.x == 10, "uniform init x");
  __CPROVER_assert(p.y == 20, "uniform init y");
  int arr[]{1, 2, 3};
  __CPROVER_assert(arr[0] + arr[1] + arr[2] == 6, "array init");
  return 0;
}
