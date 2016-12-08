
void f() {}

int main()
{
  /**
   * This is a test case for the unwind operation of goto-instrument;
   * every loop will be unwound K times
   **/
  const unsigned K=10;

  const unsigned n=100;
  unsigned c=0, i;

  for(i=1; i<=n; i++)
  {
    f();
    c++;
  }

  unsigned eva=n;
  if(K<eva) eva=K;

  __CPROVER_assert(c==eva, "Simple loop unwind (1)");

}
