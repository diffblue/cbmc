int main()
{
  int A[0] = {};
  int i;
  if(A[i] == 1)
    __CPROVER_assert(0, "");
}
