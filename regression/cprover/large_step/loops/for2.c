int main()
{
  for(int x = 0; x != 10; x++)
  {
  }

  __CPROVER_assert(0, "property 1"); // should fail

  return 0;
}
