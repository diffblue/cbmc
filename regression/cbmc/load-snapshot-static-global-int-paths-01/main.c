int x;
int y;

int main()
{
  if(nondet_int())
  {
    y = 1;
  }
  else
  {
    y = 2;
  }

  assert(x == 1);
  assert(y == 1 || y == 2);

  return 0;
}
