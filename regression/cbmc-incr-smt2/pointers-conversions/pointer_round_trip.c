int f(int x)
{
  void *p = (void *)x;
  int r = (int)p;
  return r;
}

int main()
{
  int a = f(5);
  __CPROVER_assert(a == 5, "a == 5: expected success");
  __CPROVER_assert(a != 5, "a != 5: expected failure");
}
