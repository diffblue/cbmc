int main()
{
  int unknown;
  int a = 10;

  int *p = &a;

  if(unknown)
    a = 15;

  int q = *p;

  __CPROVER_assert(q == a, "assertion q == a");
}
