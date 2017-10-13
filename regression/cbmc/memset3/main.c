#include <string.h>
#include <stdlib.h>
#include <assert.h>

int main()
{
  int *A=malloc(sizeof(int)*4);

  memset(A+20, 0, sizeof(int)); // out-of-bounds

  return 0;
}
