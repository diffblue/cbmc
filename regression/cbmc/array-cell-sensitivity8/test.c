#include <assert.h>
#include <stdlib.h>

int main(int argc, char **argv)
{
  int array[10];
  long long *ptr = argc % 2 ? (long long *)&array[0] : (long long *)&argc;
  ptr[argc] = 1;
  ptr[1] = argc;
  assert(array[1] == argc);
}
