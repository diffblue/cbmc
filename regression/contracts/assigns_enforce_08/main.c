void f1(int *x) __CPROVER_assigns(*x)
{
  int *a = x;
  f2(&a);
}
void f2(int **y) __CPROVER_assigns(**y)
{
  **y = 5;
}

int main()
{
  int n = 3;
  f1(&n);

  return 0;
}
