int x;

int main()
{
  int *p;
  __CPROVER_assume(*p == 10);
  p = &x;
  // not provable, since p may have pointed elsewhere
  __CPROVER_assert(*p == 10, "property 1");

  return 0;
}
