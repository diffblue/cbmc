int main()
{
  // clang-format off
  // no side effects!
  int j;
  int a[5] = {0 , 0, 0, 0, 0};
  assert(__CPROVER_forall { int i;  ({ ( 0 <= i && i < 4) ==> ({ int k = j; if(j < 0 || j > i) k = 1;  ( a[k] == 0); }); }) });
  // clang-format on

  return 0;
}
