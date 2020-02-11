int main()
{
  __CPROVER_bool property = (__CPROVER_bool)1;

  while(1)
  {
    __CPROVER_assume(property == 1);
    property = 0;
    __CPROVER_assert(property == 1, "property");
  }
  return 0;
}
