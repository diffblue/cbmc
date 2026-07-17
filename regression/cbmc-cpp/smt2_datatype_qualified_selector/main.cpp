struct S
{
  int x;
  int y;
};

int main()
{
  S s;
  s.x = 1;
  s.y = 2;
  S t = s;
  t.x = 3;
  __CPROVER_assert(t.y == 2 && t.x == 3, "ok");
  __CPROVER_assert(t.x == 1, "fail");
  return 0;
}
