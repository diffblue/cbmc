// Test that branch pruning works with loop-generated assumes
// (unwinding assertions generate assumes on the loop counter).

int main()
{
  int a[5] = {10, 20, 30, 40, 50};
  int sum = 0;

  for(int i = 0; i < 5; i++)
    sum += a[i];

  __CPROVER_assert(sum == 150, "sum of array");

  return 0;
}
