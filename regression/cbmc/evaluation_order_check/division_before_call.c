int b = 0;

int f(void)
{
  b = 1;
  return 0;
}

int main()
{
  int a = 10;
  int j = a / b + f();
  __CPROVER_assert(j == 10, "j == 10");
  return 0;
}
