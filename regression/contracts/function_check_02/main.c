// function_check_02

// This test checks the use of quantifiers in ensures clauses.
// A known bug (resolved in PR #2278) causes the use of quantifiers
// in ensures to fail.

// clang-format off
int initialize(int *arr)
  __CPROVER_assigns(__CPROVER_POINTER_OBJECT(arr))
  __CPROVER_ensures(
    __CPROVER_forall {
      int i;
      (0 <= i && i < 10) ==> arr[i] == i
    }
  )
// clang-format on
{
  for(int i = 0; i < 10; i++)
  {
    arr[i] = i;
  }

  return 0;
}

int main()
{
  int arr[10];
  initialize(arr);
}
