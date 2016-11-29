void main()
{
  unsigned int N;
  __CPROVER_assume(N>0);

  unsigned int j,k;
  int matrix[N], max;

  max = __VERIFIER_nondet_int();
  for(j=0;j<N;j++)
  {
    matrix[j] = __VERIFIER_nondet_int();

    if(matrix[j]>=max)
      max = matrix[j];
  }

  assert(matrix[0]<max);
}
