int x;

int main()
{
  for(x = 0; x != 1000; x++)
  {
    // deep failure
    __CPROVER_assert(x != 100000, "failing assertion");
  }

  return 0;
}
