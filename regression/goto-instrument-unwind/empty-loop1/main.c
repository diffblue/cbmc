
int main()
{
  /**
   * This is a test case for the unwind operation of goto-instrument;
   * every loop will be unwound K times
   **/
  const unsigned K=10;

  const unsigned n=100;
  unsigned i=0;

  while(++i<n)
  {
  }

  unsigned eva=n;
  if(K<eva) eva=K;

  __CPROVER_assert(i==eva, "Empty loop unwind (1)");

}
