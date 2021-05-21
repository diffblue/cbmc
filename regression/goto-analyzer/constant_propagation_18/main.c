int main()
{
  int i = 1;
  int *p = &i;
  __CPROVER_assert(*p == 1, "assertion *p == 1");
}
