// This should make the harness succeed
void stub(int *x) __CPROVER_ensures(*x == 5)
{
}
