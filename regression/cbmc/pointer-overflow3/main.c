#include <stdlib.h>

int main()
{
  int *p = malloc(sizeof(int) * 5);
  int *p2 = p + 10; // undefined behavior for indexing out of bounds
  int *p3 = p - 10; // undefined behavior for indexing out of bounds

  int arr[5];
  int *p4 = arr + 10; // undefined behavior for indexing out of bounds
  int *p5 = arr - 10; // undefined behavior for indexing out of bounds
  return 0;
}
