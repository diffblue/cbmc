#include <stdbool.h>
#include <stdlib.h>

#define MAX_LEN 10

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
  if(0 < len)
    found_four |= (arr[0] == 4);
  if(1 < len)
    found_four |= (arr[1] == 4);
  if(2 < len)
    found_four |= (arr[2] == 4);
  if(3 < len)
    found_four |= (arr[3] == 4);
  if(4 < len)
    found_four |= (arr[4] == 4);
  if(5 < len)
    found_four |= (arr[5] == 4);
  if(6 < len)
    found_four |= (arr[6] == 4);
  if(7 < len)
    found_four |= (arr[7] == 4);
  if(8 < len)
    found_four |= (arr[8] == 4);

  if(9 < len)
    found_four |= (arr[9] == 4);

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
