int main()
{
  struct S
  {
    int a[2];
    int b;
  } s;
  s.b = 1;
  __CPROVER_assert(s.b == 1, "member");
  __CPROVER_assert(s.b != 1, "fails");
  return 0;
}
