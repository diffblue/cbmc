int main()
{
  // clang-format off
  // no side effects!
  int j = 0;
  int a[5] = {0 , 0, 0, 0, 0};
  assert(__CPROVER_forall { int i;  ({ int j = i; i=i; if(i < 0 || i >4) i = 1;  ( a[i] < 5); }) });
  // clang-format on

  return 0;
}
