int main()
{
  int a, b;

  if(a >= 5)
    b = 1;
  else
    b = 0;

  __CPROVER_assert(b == (a >= 5), "property 1"); // should pass
  __CPROVER_assert(b != (a >= 5), "property 2"); // should fail

  return 0;
}
