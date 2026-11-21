int x;

int main()
{
  for(x = 0; x < 100; x++)
  {
    int z = 123;
    __CPROVER_assert(
      z >= 0, "property 1");           // true independently of loop entry state
    __CPROVER_assert(0, "property 2"); // fails
  }

  return 0;
}
