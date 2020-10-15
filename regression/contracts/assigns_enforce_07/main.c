void f1(int *x1, int *y1, int *z1) __CPROVER_assigns(*x1, *y1, *z1)
{
  f2(x1, y1, z1);
}

void f2(int *x2, int *y2, int *z2) __CPROVER_assigns(*x2, *y2, *z2)
{
  f3(x2, y2, z2);
}

void f3(int *x3, int *y3, int *z3) __CPROVER_assigns(*y3, *z3)
{
  *x3 = *x3 + 1;
  *y3 = *y3 + 1;
  *z3 = *z3 + 1;
}

int main()
{
  int p = 1;
  int q = 2;
  int r = 3;

  for(int i = 0; i < 3; ++i)
  {
    if(i == 0)
    {
      f1(&p, &q, &r);
    }
    if(i == 1)
    {
      f2(&p, &q, &r);
    }
    if(i == 2)
    {
      f3(&p, &q, &r);
    }
  }

  return 0;
}
