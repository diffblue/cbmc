int x;

int main()
{
  for(x = 0; x < 100; x++)
  {
    __CPROVER_assert(0, "property 1"); // fails
  }

  // implied by loop condition
  __CPROVER_assert(x >= 100, "property 2");

  return 0;
}
