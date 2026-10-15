int main()
{
  int x = 1;
  __CPROVER_assert(x == 0, "expected fail");
}
