
void f() {}

int main()
{
  /**
   * This is a test case for the unwind operation of goto-instrument;
   * every loop will be unwound K times
   **/
  const unsigned K=100;
  
  const unsigned n=10;
  unsigned c=0, i;

  i=1;
  do
  {
    f();
    c++;
    i++;
  } while(i<=n);

  unsigned eva=n;
  if(K<eva) eva=K;
  
  __CPROVER_assert(c==eva, "do-while loop unwind (1)");

}
