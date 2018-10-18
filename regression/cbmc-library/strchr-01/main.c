#include <assert.h>
#include <string.h>

int main()
{
  // "The terminating null character is considered to be part of the string."

  char arr[] = {'a', 'a', 'a', 0};
  assert(strchr(arr, 0) == arr + sizeof(arr) - 1);
  assert(strrchr(arr, 0) == arr + sizeof(arr) - 1);
  assert(strchr(arr, 'a') == arr);
  assert(strrchr(arr, 'a') == arr + 2);
  assert(strchr(arr, 'z') == 0);
  assert(strrchr(arr, 'z') == 0);
}
