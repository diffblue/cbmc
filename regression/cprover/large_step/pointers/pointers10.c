int main()
{
  int *p; // unconstrained
  int x;

  if(p == &x) // address taken
  {
    *p = 123;
    __CPROVER_assert(x == 123, "property 1"); // should pass
  }

  return 0;
}
