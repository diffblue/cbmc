int main()
{
  int A[] = {1, 1};
  int i;
  __CPROVER_assert(i < 0 || i > 1 || A[i] == 1, "valid access into array of 1");
  __CPROVER_assert(A[i] == 1, "possible out-of-bounds access");
  return 0;
}
