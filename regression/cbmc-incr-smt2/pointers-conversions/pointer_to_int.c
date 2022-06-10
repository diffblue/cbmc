int cmp(const void *p1, const void *p2)
{
  int x = *(int *)p1;
  int y = *(int *)p2;

  return (x < y) ? -1 : ((x == y) ? 0 : 1);
}

int main()
{
  int a = 5;
  int b = 6;
  int c = 7;

  __CPROVER_assert(cmp(&a, &b) == -1, "expected result == -1: success");
  __CPROVER_assert(cmp(&c, &b) == 1, "expected result == 1: success");
  __CPROVER_assert(cmp(&c, &c) == 0, "expected result == 0: success");
  __CPROVER_assert(cmp(&c, &c) == 1, "expected result == 1: failure");
}
