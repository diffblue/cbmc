int cmp(int i1, int i2)
  // clang-format off
  __CPROVER_ensures((i1 == i2) ==> (__CPROVER_return_value == 0))
  __CPROVER_ensures((i1 != i2) ==> (__CPROVER_return_value == -1))
// clang-format on
{
  if(i1 == i2)
    return 0;
  else
    return -1;
}

int main()
{
  int ret = -1;
  ret = cmp(0, 0);
  __CPROVER_assert(ret == 0, "expecting SUCCESS");
  ret = cmp(0, 1);
  __CPROVER_assert(ret == 0, "expecting FAILURE");
  __CPROVER_assert(ret == -1, "expecting SUCCESS");
  __CPROVER_assert(0, "expecting FAILURE");
  return 0;
}
