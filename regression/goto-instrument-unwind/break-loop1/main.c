
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
  unsigned tres=K/2;;

  for(i=1; i<=n; i++)
  {
    f();
    c++;
    if(i==tres)
      break;
  }

  unsigned eva=n;
  if(K<eva) eva=K;
  if(tres<eva) eva=tres;

  __CPROVER_assert(c==eva, "break a loop unwind (1)");

}
