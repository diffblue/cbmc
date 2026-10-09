template <int N>
struct S
{
  static constexpr int size = N;
  int arr[size];
};

int main()
{
  S<3> s;
  s.arr[0] = 10;
  s.arr[1] = 20;
  s.arr[2] = 30;
  __CPROVER_assert(s.arr[0] == 10, "arr[0]");
  __CPROVER_assert(s.arr[1] == 20, "arr[1]");
  __CPROVER_assert(s.arr[2] == 30, "arr[2]");
  return 0;
}
