int main()
{
  int x;
  if(x >= 5)
  {
    __CPROVER_assert(x >= 5, "property 1"); // should pass
    __CPROVER_assert(0, "property 2");      // should fail
  }
  else
  {
    __CPROVER_assert(x < 5, "property 3"); // should pass
    __CPROVER_assert(0, "property 4");     // should fail
  }
}
