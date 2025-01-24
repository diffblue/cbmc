void foo(int *x, int *y, int **z)
  // clang-format off
__CPROVER_requires(__CPROVER_is_fresh(x, sizeof(int)))
__CPROVER_requires(__CPROVER_is_fresh(y, sizeof(int)))
__CPROVER_requires(__CPROVER_is_fresh(z, sizeof(int*)))
__CPROVER_requires(__CPROVER_pointer_equals(*z, x))
__CPROVER_assigns(*z)
__CPROVER_ensures(__CPROVER_pointer_equals(*z, y))
// clang-format on
{
  *z = y;
}

int main()
{
  int *x;
  int *y;
  int **z;
  foo(x, y, z);
  return 0;
}
