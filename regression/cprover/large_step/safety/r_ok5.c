int x;

int main()
{
  __CPROVER_assert(__CPROVER_r_ok(&x), "property 1");
  return 0;
}
