
int main(void)
{
  int x = 1;
  int y = 3;
  int nondet;

  if(nondet)
    y = 5;
  if(nondet)
    x = 2;

  __CPROVER_assert(x < y, "x < y");
  __CPROVER_assert(x <= y, "x <= y");
  __CPROVER_assert(y > x, "y > x");
  __CPROVER_assert(y >= x, "y >= x");
}
