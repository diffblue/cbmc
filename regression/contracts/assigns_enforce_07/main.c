void f1(int *x, int *y, int *z) __CPROVER_assigns(*x, *y)
{
  *x = *x + 1;
  *y = *y + 1;
}

void f2(int *x, int *y, int *z) __CPROVER_assigns(*x, *y)
{
  *x = *x + 1;
  *y = *y + 1;
}

void f3(int *x, int *y, int *z) __CPROVER_assigns(*x, *y, *z)
{
  *x = *x + 1;
  *y = *y + 1;
  *z = *z + 1;
}

void f(int *x, int *y, int *z) __CPROVER_assigns(*x, *y)
{
  for(int i = 0; i < 3; ++i)
  {
    if(i == 0)
    {
      f1(x, y, z);
    }
    if(i == 1)
    {
      f2(x, y, z);
    }
    if(i == 2)
    {
      f3(x, y, z);
    }
  }
}

int main()
{
  int p = 1;
  int q = 2;
  int r = 3;
  f(&p, &q, &r);
  return 0;
}
