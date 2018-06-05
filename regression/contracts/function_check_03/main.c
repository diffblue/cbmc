// function_check_03

// This extends function_check_02's test of quantifiers in ensures
// and adds in a loop invariant which can be used to prove the ensures.
// This currently fails because side-effect checking in loop invariants is
// incorrect.

void initialize(int *arr, int len)
  __CPROVER_ensures(
    __CPROVER_forall {int i; (0 <= i && i < len) ==> arr[i] == i}
  )
{
  for(int i = 0; i < len; i++)
    __CPROVER_loop_invariant(
      __CPROVER_forall {int j; (0 <= j && j < i) ==> arr[j] == j}
    )
  {
    arr[i] = i;
  }
}

int main()
{
  int arr[10];
  initialize(arr, 10);
}
