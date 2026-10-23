extern "C" void __CPROVER_assert(bool, const char *);
typedef unsigned char uint8_t;
struct A
{
  static constexpr uint8_t sz[3] = {[0] = 1, [1] = 8, [2] = 1};
};
int arr[4] = {[0] = 3, [1] = 4, [2] = 7, [3] = 8};
// enumerators as designators, an enumerator as the bound (user-reported
// Issue 3, second shape: the bound reached symex as a c_enum_tag constant,
// the designated list was dropped by the class-scope initializer path)
enum
{
  D_INVALID,
  D_U64,
  D_I8,
  D_COUNT
};
struct B
{
  static constexpr uint8_t sz[D_COUNT] =
    {[D_INVALID] = 1, [D_U64] = 8, [D_I8] = 1};
  static constexpr int n = D_COUNT;
};
int arr2[D_COUNT] = {[D_INVALID] = 0, [D_U64] = 8, [D_I8] = 2};
int main()
{
  __CPROVER_assert(
    A::sz[1] == 8, "designated array initializer (static constexpr member)");
  __CPROVER_assert(A::sz[2] == 1, "third element");
  __CPROVER_assert(
    arr[0] == 3 && arr[1] == 4 && arr[2] == 7 && arr[3] == 8,
    "global array designators");
  __CPROVER_assert(sizeof(B::sz) == 3 && B::n == 3, "enumerator bound");
  __CPROVER_assert(
    B::sz[D_INVALID] == 1 && B::sz[D_U64] == 8 && B::sz[D_I8] == 1,
    "enumerator designators");
  __CPROVER_assert(
    arr2[0] == 0 && arr2[1] == 8 && arr2[2] == 2,
    "enumerator designators, namespace scope");
  return 0;
}
