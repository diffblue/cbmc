int f1(int *x1) __CPROVER_requires(*x1 > 0 && *x1 < 20)
  __CPROVER_ensures(__CPROVER_return_value == *x1 + 2)
{
  return f2(x1) + 1;
}

int f2(int *x2) __CPROVER_requires(*x2 >= 0 && *x2 < 20)
  __CPROVER_ensures(__CPROVER_return_value == *x2 + 1)
{
  if(*x2 < 1)
    return -1; //Notice the change for the base case
  int loc = *x2 - 1;
  return f2(&loc) + 1;
}

int main()
{
  int p;
  __CPROVER_assume(p > 0 && p < 20);
  f1(&p);

  return 0;
}
