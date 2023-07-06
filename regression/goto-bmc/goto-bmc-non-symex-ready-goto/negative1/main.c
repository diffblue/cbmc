int main(int argc, char *argv[])
{
  int a[] = {0, 1, 2, 3, 4};
  __CPROVER_assert(a[0] != 0, "expected fail: 0 == 0");
  return 0;
}
