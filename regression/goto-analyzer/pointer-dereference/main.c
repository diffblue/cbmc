int main()
{
  int a = 10;
  int *p = &a;

  int q = *p;

  __CPROVER_assert(q == a, "assertion q == a");
}
