int main()
{
  int a = 10;
  int *p = &a;

  *p = 15;

  __CPROVER_assert(a == 15, "assertion a == 15");
}
