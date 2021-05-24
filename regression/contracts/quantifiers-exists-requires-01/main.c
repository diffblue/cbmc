#include <stdbool.h>
#include <stdlib.h>

#define MAX_LEN 64

// clang-format off
bool f1(int *arr, int len)
  __CPROVER_requires(
    len > 0 ==> __CPROVER_exists {
      int i;
      // test enforcement with symbolic bound
      (0 <= i && i < len) && arr[i] == 4
    }
  )
  __CPROVER_ensures(
    __CPROVER_return_value == true
  )
// clang-format on
{
  bool found_four = false;
  for(int i = 0; i <= MAX_LEN; i++)
  {
    if(i < len)
      found_four |= (arr[i] == 4);
  }

  // clang-format off
  return (len > 0 ==> found_four);
  // clang-format on
}

int main()
{
  int len;
  __CPROVER_assume(0 <= len && len <= MAX_LEN);

  int *arr = malloc(len * sizeof(int));
  f1(arr, len);
}
