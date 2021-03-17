void f1(int *x1, int *y1, int *z1);

void f2(int *x2, int *y2, int *z2);

void f3(int *x3, int *y3, int *z3);

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
