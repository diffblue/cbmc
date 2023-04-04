int main()
{
  int A[5] = {0, 1, 2, 3, 4};
  for(int *iter = &A[0]; iter < &A[5]; ++iter)
    __CPROVER_assert(*iter == iter - &A[0], "values match");
}
