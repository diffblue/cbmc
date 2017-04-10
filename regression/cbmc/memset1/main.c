#include <string.h>
#include <stdlib.h>
#include <assert.h>

int main()
{
  int A[5];
  memset(A, 0, sizeof(int)*5);
  assert(A[0]==0);
  assert(A[1]==0);
  assert(A[2]==0);
  assert(A[3]==0);
  assert(A[4]==0);

  A[3]=42;
  memset(A, 0xFFFFFF01, sizeof(int)*3);
  assert(A[0]==0x01010101);
  assert(A[1]==0x01010111);
  assert(A[2]==0x01010101);
  assert(A[3]==42);
  assert(A[4]==0);

  int *B=malloc(sizeof(int)*2);
  memset(B, 2, sizeof(int)*2);
  assert(B[0]==0x02020202);
  assert(B[1]==0x02020202);

  return 0;
}
