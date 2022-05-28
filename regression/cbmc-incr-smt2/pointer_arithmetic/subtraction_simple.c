#define NULL (void *)0

int main()
{
  int *x;
  int *y = x - 2;
  __CPROVER_assume(x != NULL);
  __CPROVER_assume(y != NULL);

  __CPROVER_assert(y == x, "expected failure after pointer manipulation");
  __CPROVER_assert(y != x, "expected successful after pointer manipulation");
}
