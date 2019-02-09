extern int nondet_int();
int main()
{
  int x = nondet_int();
  __CPROVER_assume(0 <= x && x <= 1);
  int y = 0;
  while(y < 5) // main.0
  {
    y++;
    if(nondet_int())
      break;
  }
  while(1) // main.1
  {
    if(nondet_int())
      break;
  }
  while(x < 4) // main.3
  {
    while(1) // main.2
    {
      if(nondet_int())
        break;
    }
    x = x + 1;
    assert(x < 4);
  }
}
