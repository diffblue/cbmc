#include <string.h>

int main()
{
  char bufferA[10], bufferB[10];

  // ok
  memcpy(bufferA, bufferB, 10);

  // not ok, overlap, should use memmove
  memcpy(bufferA, bufferA + 1, 9);

  // ok, no overlap
  memcpy(bufferA, bufferA + 5, 5);

  // out of bounds
  memcpy(bufferA + 1, bufferB, 10);
}
