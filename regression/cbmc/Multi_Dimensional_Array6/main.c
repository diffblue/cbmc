// from SV-COMP matrix_false.i

extern unsigned int __VERIFIER_nondet_uint();
extern int __VERIFIER_nondet_int();

int main()
{
  unsigned int N_LIN=__VERIFIER_nondet_uint();
  unsigned int N_COL=__VERIFIER_nondet_uint();
  unsigned int j,k;
  int matriz[N_COL][N_LIN], maior;

  maior = __VERIFIER_nondet_int();
  for(j=0;j<N_COL;j++)
    for(k=0;k<N_LIN;k++)
    {
       matriz[j][k] = __VERIFIER_nondet_int();

       if(matriz[j][k]>maior)
          maior = matriz[j][k];
    }

  for(j=0;j<N_COL;j++)
    for(k=0;k<N_LIN;k++)
      __CPROVER_assert(matriz[j][k]<=maior, "");

  __CPROVER_assert(matriz[0][0]<maior, "");
}
