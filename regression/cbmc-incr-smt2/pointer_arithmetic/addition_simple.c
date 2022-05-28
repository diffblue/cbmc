#define NULL (void *)0

int main()
{
  int *x;
  int *y = x + 1;
  __CPROVER_assume(x != NULL);
  __CPROVER_assume(y != NULL);

  __CPROVER_assert(y == x, "expected false after pointer manipulation");
  __CPROVER_assert(y != x, "expected true");
}
