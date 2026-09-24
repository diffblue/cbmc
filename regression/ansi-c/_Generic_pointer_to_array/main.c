#include <stdbool.h>

int main(void)
{
  // Test case from issue #8690
  // A generic selection on a value of type int(*)[5] should match an arm for
  // int(*)[]. regression/ansi-c runs under goto-cc (compile only), so we use
  // _Static_assert / no-default arms: a wrong selection becomes a translation
  // error rather than a never-evaluated run-time assert.

  // No-default arms: a non-match is a CONVERSION ERROR at compile time.
  int arr[5];
  (void)_Generic(&arr, int(*)[] : true);

  // Different array sizes - should all match int(*)[].
  int arr2[10];
  (void)_Generic(&arr2, int(*)[] : true);

  int arr3[1];
  (void)_Generic(&arr3, int(*)[] : true);

  // Character arrays: verify the selected value via a compile-time check so
  // the default-fallback arm is actually exercised.
  char carr[20];
  _Static_assert(_Generic(&carr, char(*)[] : 1, default : 0) == 1, "char(*)[]");

  // Default case as fallback: an int* must not match int(*)[], so the result
  // is the default value 2.
  int *ptr;
  _Static_assert(_Generic(ptr, int(*)[] : 1, default : 2) == 2, "default");

  // Pointer to array of specific size should also match int(*)[].
  int(*ptr_to_arr)[5] = &arr;
  (void)_Generic(ptr_to_arr, int(*)[] : true);

  return 0;
}
