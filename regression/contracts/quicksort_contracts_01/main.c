// quicksort_contracts_01

// This test checks the correctness of a quicksort implementation using explicit
// ghost state.

// This test currently fails for a variety of reasons, including:
// (1) Lack of support for quantifiers in ensures statements.
// (2) Lack of support for reading from memory in loop invariants (under some
// circumstances)

#include <assert.h>
#include <stdlib.h>
#include <string.h>

void swap(int *a, int *b)
{
  *a ^= *b;
  *b ^= *a;
  *a ^= *b;
}

int partition(int arr_ghost[], int arr[], int len)
  __CPROVER_requires(
    __CPROVER_forall {int i; (0 <= i && i < len) ==> arr_ghost[i] == arr[i]} &&
   len > 0 &&
    1 == 1
  )
  __CPROVER_ensures(
    __CPROVER_forall {int i; (0 <= i && i < len) ==> __CPROVER_exists {int j; 0 <= j && j < len && arr_ghost[i] == arr[j]}} &&
    __CPROVER_forall {int i; (0 <= i && i < len) ==> __CPROVER_exists {int j; 0 <= j && j < len && arr[i] == arr_ghost[j]}} &&
    0 <= __CPROVER_return_value && __CPROVER_return_value < len &&
    __CPROVER_forall {int i; (0 <= i && i <= __CPROVER_return_value) ==> arr[i] <= arr[__CPROVER_return_value]} &&
    __CPROVER_forall {int i; (__CPROVER_return_value <= i && i < len) ==> arr[__CPROVER_return_value] <= arr[i]} &&
    1 == 1
  )
{
  int h = len - 1;
  int l = 0;

  int pivot_idx = len / 2;
  int pivot = arr[pivot_idx];

  while(h > l)
    __CPROVER_loop_invariant(
        0 <= l && l <= pivot_idx && pivot_idx <= h && h < len &&
      arr[pivot_idx] == pivot &&
      __CPROVER_forall {int i; (0 <= i && i < l) ==> arr[i] <= pivot} &&
      __CPROVER_forall {int i; (h < i && i < len) ==> pivot <= arr[i]} &&
      1 == 1
    )
  {
    if(arr[h] <= pivot && arr[l] >= pivot)
    {
      swap(arr + h, arr + l);
      if(pivot_idx == h)
      {
        pivot_idx = l;
        h--;
      }
      if(pivot_idx == l)
      {
        pivot_idx = h;
        l++;
      }
    }
    else if(arr[h] <= pivot)
    {
      l++;
    }
    else
    {
      h--;
    }
  }
  return pivot_idx;
}

void quicksort(int arr_ghost[], int arr[], int len)
  __CPROVER_requires(
    __CPROVER_forall {int i; (0 <= i && i < len) ==> arr_ghost[i] == arr[i]} &&
    1 == 1
  )
  __CPROVER_ensures(
    __CPROVER_forall {int i; (0 <= i && i < len) ==> __CPROVER_exists {int j; 0 <= j && j < len && arr_ghost[i] == arr[j]}} &&
    __CPROVER_forall {int i; (0 <= i && i < len) ==> __CPROVER_exists {int j; 0 <= j && j < len && arr[i] == arr_ghost[j]}} &&
    __CPROVER_forall {int i; (0 <= i && i < len) ==> __CPROVER_forall {int j; (i <= j && j < len) ==> arr[i] <= arr[j]}} &&
    1 == 1
  )
{
  if(len <= 1)
  {
    return;
  }
  int *new_ghost = malloc(len * sizeof(int));
  memcpy(new_ghost, arr, len * sizeof(int));

  int pivot_idx = partition(new_ghost, arr, len);

  memcpy(new_ghost, arr, len * sizeof(int));

  quicksort(new_ghost, arr, pivot_idx);
  quicksort(new_ghost, arr + pivot_idx + 1, len - pivot_idx - 1);

  free(new_ghost);
}

int main()
{
  int arr[5] = {1, 2, 3, 0, 4};
  int arr_ghost[5] = {1, 2, 3, 0, 4};
  quicksort(arr_ghost, arr, 5);
}
