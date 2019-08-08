#include <assert.h>
#include <stdlib.h>

int main(int argc, char **argv)
{
  int array[10];
  long long other;
  long long *ptr = argc % 2 ? (long long *)&array[0] : &other;
  ptr[argc] = 1;
  ptr[1] = argc;
  assert(ptr[1] == argc);
  assert(array[1] == argc);
}
