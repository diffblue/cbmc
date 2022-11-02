void f1(int *x1, int *y1, int *z1) __CPROVER_assigns(*x1, *y1)
{
  f2(x1, y1, z1);
}

void f2(int *x2, int *y2, int *z2) __CPROVER_assigns(*y2, *z2)
{
  *y2 = 5;
  *z2 = 5;
}

int main()
{
  int p = 1;
  int q = 2;
  int r = 3;
  f1(&p, &q, &r);

  return 0;
}
