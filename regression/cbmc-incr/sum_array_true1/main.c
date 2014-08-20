extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: goto ERROR;
  }
  return;
}
extern unsigned int __VERIFIER_nondet_uint();

int main()
{
  unsigned int M = __VERIFIER_nondet_uint();
  int A[M], B[M], C[M];
  unsigned int i;

  for(i=0;i<M;i++)
    A[i] = __VERIFIER_nondet_int();

  for(i=0;i<M;i++)
    B[i] = __VERIFIER_nondet_int();

  for(i=0;i<M;i++)
     C[i]=A[i]+B[i];

  for(i=0;i<M;i++)
     __VERIFIER_assert(C[i]==A[i]+B[i]);
}
