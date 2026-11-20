struct S
{
  int x;
};

int g(int a)
{
  return a + 1;
}

int main(void)
{
  struct S s;
  s.x = g(0);
  __CPROVER_assert(s.x == 1, "ok");
  return 0;
}
