int f1(int *a, int *b) __CPROVER_assigns(*a)
{
  if(*a > 0)
  {
    int *b = a;
    *b = 5;
  }
  *b = 5;
}

int main()
{
  int m = 4;
  int n = 3;
  f1(&m, &n);

  return 0;
}
