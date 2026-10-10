int main()
{
  int *p; // unconstrained
  int x = 123;

  if(p == &x)
    __CPROVER_assert(*p == 123, "property 1"); // should pass

  return 0;
}
