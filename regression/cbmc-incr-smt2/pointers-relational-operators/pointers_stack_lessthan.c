#define NULL (void *)0

int main()
{
  int i = 12;
  int *x = &i;
  int *y = x + 1;
  int *z = x - 1;

  // Assertions on y's relation to x
  __CPROVER_assert(y != x, "y != x: expected successful");
  __CPROVER_assert(y > x, "y > x: expected successful");
  __CPROVER_assert(y < x, "y < x: expected failure");

  // Assertions on z's relation to x
  __CPROVER_assert(z != x, "z != x: expected successful");
  __CPROVER_assert(z > x, "z > x: expected failure");
  __CPROVER_assert(z < x, "z < x: expected success");
}
