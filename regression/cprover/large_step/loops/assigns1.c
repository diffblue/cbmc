int main()
{
  int x = 123;

  for(int i = 0; i < 10; i++)
  {
    // does not assign x
  }

  __CPROVER_assert(x == 123, "property 1"); // passes
}
