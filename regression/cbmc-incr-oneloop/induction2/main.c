int main()
{
  int a, b, c, x, i, temp;
  a = 1;
  b = 2;
  c = 3;
  x = 0;

  while(1)
  {
    __CPROVER_assume(x == 0);
    temp = a;
    a = b;
    b = c;
    c = temp;
    assert(x == 0);
  }
}
