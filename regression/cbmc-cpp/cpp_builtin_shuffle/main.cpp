extern "C" void __CPROVER_assert(bool, const char *);
typedef int v4 __attribute__((vector_size(16)));
int main()
{
  int x = 5;
  v4 a = {x, x + 1, x + 2, x + 3};
  v4 mask = {3, 2, 1, 0};
  // GCC's __builtin_shuffle(vec, mask): element i of the result is
  // vec[mask[i]]
  v4 b = __builtin_shuffle(a, mask);
  __CPROVER_assert(b[0] == 8 && b[3] == 5, "reversed");
  __CPROVER_assert(b[0] == 5, "WRONG (must FAIL)");
}
