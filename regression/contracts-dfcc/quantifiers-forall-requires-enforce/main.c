#include <stdbool.h>

// clang-format off
bool f1(int *arr)
  __CPROVER_requires(__CPROVER_forall {
    int i;
    (0 <= i && i < 10) ==> arr[i] == i
  })
  __CPROVER_ensures(
    __CPROVER_return_value == true
  )
// clang-format on
{
  bool is_identity = true;
  is_identity &= (arr[0] == 0);
  is_identity &= (arr[1] == 1);
  is_identity &= (arr[2] == 2);
  is_identity &= (arr[3] == 3);
  is_identity &= (arr[4] == 4);
  is_identity &= (arr[5] == 5);
  is_identity &= (arr[6] == 6);
  is_identity &= (arr[7] == 7);
  is_identity &= (arr[8] == 8);
  is_identity &= (arr[9] == 9);
  return is_identity;
}

int main()
{
  int arr[10];
  f1(arr);
}
