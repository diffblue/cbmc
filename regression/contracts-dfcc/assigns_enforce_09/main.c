void f1(int **x) __CPROVER_assigns(*x)
{
  f2(x);
}
void f2(int **y) __CPROVER_assigns(**y)
{
  **y = 5;
}

int main()
{
  int p = 3;
  int *q = &p;
  f1(&q);

  return 0;
}
