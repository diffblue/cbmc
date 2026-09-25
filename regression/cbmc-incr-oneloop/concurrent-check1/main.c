extern int nondet_int();
int main()
{
  int x = nondet_int();
  __CPROVER_assume(0 <= x && x <= 10);
  int y = 0;
  while(x > 0)
  {
    y = y + 1;
    x = x - 1;
    assert(y >= 1);
    assert(x >= 0);
  }
  assert(y >= 0);
  assert(x == 0);
}
