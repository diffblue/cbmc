extern int nondet_int();
int main()
{
  int x = nondet_int();
  __CPROVER_assume(0 <= x && x <= 1);
  while(x < 4) // main.1
  {
    int y = 5;
    while(y > 2) // main.0
      y -= 2;
    x = x + y;
    assert(x < 4);
  }
}
