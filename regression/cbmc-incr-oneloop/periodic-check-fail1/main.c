extern int nondet_int();
int main()
{
  int x = nondet_int();
  __CPROVER_assume(0 <= x && x <= 5);
  int sum = 0;
  while(x > 0)
  {
    sum = sum + x;
    x = x - 1;
  }
  assert(sum <= 10);
}
