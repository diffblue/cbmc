extern int nondet_int();
int main()
{
  int x = nondet_int();
  __CPROVER_assume(0 <= x && x <= 1);
  while(1) // main.0
  {
    if(nondet_int())
      break;
  }
  while(x < 4) // main.1
  {
    x = x + 1;
    assert(x < 4);
  }
}
