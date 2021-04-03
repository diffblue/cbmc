int main()
{
  int unknown;
  int a = 10;
  int b = 10;
  int *p = &a;

  if(unknown)
  {
    b = 15;
    *p = 15;
  }

  __CPROVER_assert(*p == b, "assertion *p == b");
}
