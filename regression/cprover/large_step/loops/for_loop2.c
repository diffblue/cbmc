int x;

int main()
{
  for(x = 0; x < 100; x++)
  {
    __CPROVER_assert(0, "property 1"); // fails
  }

  int z = 123;

  // true independently of loop exit state
  __CPROVER_assert(z >= 0, "property 2");

  return 0;
}
