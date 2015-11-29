int main()
{
  int A[1]={42};

  int ok;

  ok=((void)0,A[0]);
  __CPROVER_assert(ok==42, "");

  int * broken;

  broken=((void)0,A);
  __CPROVER_assert(broken==&(A[0]), "");

  return 0;
}
