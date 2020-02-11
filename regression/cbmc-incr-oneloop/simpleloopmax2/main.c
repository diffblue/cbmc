extern int nondet_int();
int main()
{
  int x = nondet_int();
  __CPROVER_assume(0 <= x && x <= 1);
  while(x < 4)
  {
    x = x + 1;
    assert(x <= 4);
  }
}
