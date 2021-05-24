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
  for(int i = 0; i < 10; ++i)
    is_identity &= (arr[i] == i);
  return is_identity;
}

int main()
{
  int arr[10];
  f1(arr);
}
