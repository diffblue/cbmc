int main()
{
  // clang-format off
  // no side effects!
  int j = 0;
  int a[5] = {0 , 0, 0, 0, 0};
  assert(__CPROVER_forall { int i;  ({ int j = i; int cond = i < 0 || i >4; if(cond) i = 1;  ( a[i] < 5); }) });
  // clang-format on

  return 0;
}
