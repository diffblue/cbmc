#include <assert.h>

void swap(int *a, int *b)
{
  *a ^= *b;
  *b ^= *a;
  *a ^= *b;
}

int main()
{
  int arr0, arr1, arr2, arr3, arr4;
  arr0 = 1;
  arr1 = 2;
  arr2 = 0;
  arr3 = 4;
  arr4 = 3;
  int *arr[5] = {&arr0, &arr1, &arr2, &arr3, &arr4};
  int pivot = 2;

  int h = 5 - 1;
  int l = 0;
  int r = 1;
  while(h > l)
    // clang-format off
    __CPROVER_assigns(arr0, arr1, arr2, arr3, arr4, h, l, r)
    __CPROVER_loop_invariant(
      // Turn off `clang-format` because it breaks the `==>` operator.
      h >= l &&
      0 <= l && l < 5 &&
      0 <= h && h < 5 &&
      l <= r && r <= h &&
      (r == 0 ==> arr0 == pivot) &&
      (r == 1 ==> arr1 == pivot) &&
      (r == 2 ==> arr2 == pivot) &&
      (r == 3 ==> arr3 == pivot) &&
      (r == 4 ==> arr4 == pivot) &&
      (0 < l ==> arr0 <= pivot) &&
      (1 < l ==> arr1 <= pivot) &&
      (2 < l ==> arr2 <= pivot) &&
      (3 < l ==> arr3 <= pivot) &&
      (4 < l ==> arr4 <= pivot) &&
      (0 > h ==> arr0 >= pivot) &&
      (1 > h ==> arr1 >= pivot) &&
      (2 > h ==> arr2 >= pivot) &&
      (3 > h ==> arr3 >= pivot) &&
      (4 > h ==> arr4 >= pivot)
    )
    __CPROVER_decreases(h - l)
    // clang-format on
    {
      if(*(arr[h]) <= pivot && *(arr[l]) >= pivot)
      {
        swap(arr[h], arr[l]);
        if(r == h)
        {
          r = l;
          h--;
        }
        else if(r == l)
        {
          r = h;
          l++;
        }
        else
        {
          h--;
          l++;
        }
      }
      else if(*(arr[h]) <= pivot)
      {
        l++;
      }
      else
      {
        h--;
      }
    }

  // Turn off `clang-format` because it breaks the `==>` operator.
  /* clang-format off */
  assert(0 <= r && r < 5);
  assert(*(arr[r]) == pivot);
  assert(0 < r ==> arr0 <= pivot);
  assert(1 < r ==> arr1 <= pivot);
  assert(2 < r ==> arr2 <= pivot);
  assert(3 < r ==> arr3 <= pivot);
  assert(4 < r ==> arr4 <= pivot);
  assert(0 > r ==> arr0 >= pivot);
  assert(1 > r ==> arr1 >= pivot);
  assert(2 > r ==> arr2 >= pivot);
  assert(3 > r ==> arr3 >= pivot);
  assert(4 > r ==> arr4 >= pivot);
  /* clang-format on */

  return r;
}
