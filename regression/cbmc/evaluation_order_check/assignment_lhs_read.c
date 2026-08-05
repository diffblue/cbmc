int a[2];
int i;

int f(void)
{
  i = 1;
  return 1;
}

int main()
{
  a[i] = f();
  __CPROVER_assert(a[1] == 1, "a[1] == 1");
  return 0;
}
