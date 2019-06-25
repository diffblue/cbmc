// This should make the harness succeed
void stub(int *x) __CPROVER_requires(*x == 1) __CPROVER_ensures(*x == 5)
{
}
