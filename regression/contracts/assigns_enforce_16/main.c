void foo(int *xp) __CPROVER_assigns(*xp)
{
  {
    int y;
    y = 2;
  }
  int z = 3;
  *xp = 1;
}

int main()
{
  int *xp = malloc(sizeof(*xp));
  foo(xp);
  return 0;
}
