int g(int *x) __CPROVER_requires(__CPROVER_is_fresh(x, sizeof(int)))
  __CPROVER_assigns(*x)
    __CPROVER_ensures(*x == 1 && __CPROVER_return_value == 0)
{
  *x = 1;
  return 0;
}

void h(int *x)
{
  g(x);
  g(x);
}

void f(int *a, int n)
  __CPROVER_requires(__CPROVER_is_fresh(a, sizeof(int)) && 0 <= n && n < 10)
    __CPROVER_assigns(*a) __CPROVER_ensures(n == 0 || *a == 1)
{
  int i = 0;
  while(i < n)
    // clang-format off
    __CPROVER_loop_invariant(0 <= i && i <= n && (i == 0 || *a == 1))
    __CPROVER_decreases(n - i)
    // clang-format on
    {
      h(a);
      i++;
    }
}

int main()
{
  int a;
  int n;
  f(&a, n);
  return 0;
}
