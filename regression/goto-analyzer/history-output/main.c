int main(int argc, char **argv)
{
  int nondet1;
  int nondet2;
  int x;

  if(nondet1)
  {
    // Taking this path the assertion clearly holds
    x = 1;
  }
  else
  {
    if(nondet2)
    {
      // Taking this path the assertion clearly fails
      x = 0;
    }
    // Not taking the branch means the assertion is unknown
    // because x is non-deterministic
  }

  __CPROVER_assert(x, "assertion x");

  return 0;
}
