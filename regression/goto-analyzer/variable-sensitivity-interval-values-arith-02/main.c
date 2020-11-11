
int main(void)
{
  int x;
  int y;
  int z;
  int nondet;

  x = 1;
  y = 2;

  if(nondet)
  {
    y = 3;
  }

  z = x + y;

  return 0;
}
