int main()
{
  int A[0] = {};
  int i = __VERIFIER_nondet_int();
  if(A[i] == 1)
    __CPROVER_assert(0, "");
}
