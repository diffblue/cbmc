
void f() {}
void f2() {}

int main()
{
  /**
   * This is a test case for the unwind operation of goto-instrument;
   * every loop will be unwound K times
   **/
  const unsigned K=10;

  const unsigned n=6;
  unsigned c=0, i;

  for(i=1; i<=n; i++)
  {
    f();
    c++;

    // the nested loop
    unsigned j, c2=0;
    for(j=1; j<=i; j++)
    {
      f2();
      c2++;
    }
    unsigned eva2=i;
    if(K<eva2) eva2=K;

    __CPROVER_assert(c2==eva2, "Nested loops unwind (2): the inner one");

  }

  unsigned eva=n;
  if(K<eva) eva=K;

  __CPROVER_assert(c==eva, "Nested loops unwind (2)");

}
