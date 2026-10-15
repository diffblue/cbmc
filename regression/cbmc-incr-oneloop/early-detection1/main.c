// Test that incremental checking detects failures before symex completes.
extern int nondet_int();

int compute(int *arr, int n)
{
  int sum = 0;
  for(int i = 0; i < n; i++)
  {
    sum += arr[i];
    assert(sum < 1000000);
  }
  return sum;
}

int main()
{
  int n = nondet_int();
  __CPROVER_assume(n >= 1 && n <= 50);

  int arr[50];
  for(int i = 0; i < 50; i++)
  {
    arr[i] = nondet_int();
    __CPROVER_assume(arr[i] >= 0 && arr[i] <= 100000);
  }

  int result = compute(arr, n);
  assert(result >= 0);
}
