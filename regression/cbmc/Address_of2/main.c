int main()
{
  int A[42][13];

  __CPROVER_assert(&(A[0][0])+13+1==&(A[1][1]), "");
  __CPROVER_assert((&A)[0]==&(A[0]), "");
  __CPROVER_assert((&(A[0])+1)[0]+1 == &(A[1][1]), "");

  return 0;
}
