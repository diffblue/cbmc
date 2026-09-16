extern "C" void __CPROVER_assert(bool, const char *);
typedef unsigned char uint8_t;
struct A
{
  static constexpr uint8_t sz[3] = {[0] = 1, [1] = 8, [2] = 1};
};
int arr[4] = {[0] = 3, [1] = 4, [2] = 7, [3] = 8};
int main()
{
  __CPROVER_assert(A::sz[1] == 8, "designated array initializer (static constexpr member)");
  __CPROVER_assert(A::sz[2] == 1, "third element");
  __CPROVER_assert(arr[0] == 3 && arr[1] == 4 && arr[2] == 7 && arr[3] == 8, "global array designators");
  return 0;
}
