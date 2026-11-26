extern "C" void __CPROVER_assert(bool, const char *);
const int global_size = 2;
enum count
{
  one = 1,
  two,
  three
};
int f(int v)
{
  // [expr.const]/8, 9: const objects of integral or enumeration type with a
  // constant initializer are usable in constant expressions
  const int n = 3;
  const int a[n] = {1, v, 3};
  const count c = three;
  int b[c + global_size] = {0};
  const int m = n * 2;
  char d[m];
  __CPROVER_assert(sizeof(a) == 3 * sizeof(int), "local");
  __CPROVER_assert(sizeof(b) == 5 * sizeof(int), "enumeration and global");
  __CPROVER_assert(sizeof(d) == 6, "initialized from another");
  return a[1] + b[4];
}
int main()
{
  __CPROVER_assert(f(4) == 4, "value");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
