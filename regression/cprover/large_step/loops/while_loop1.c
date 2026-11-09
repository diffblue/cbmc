int x;

int main()
{
  x = 0;

  while(x < 100)
  {
    int z = 123;
    __CPROVER_assert(
      z >= 0, "property 1");           // true independently of loop entry state
    __CPROVER_assert(0, "property 2"); // fails
    x++;
  }

  return 0;
}
