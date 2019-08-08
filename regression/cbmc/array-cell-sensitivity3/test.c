#include <assert.h>

int main(int argc, char **argv)
{
  int array[10];
  int *ptr = argc % 2 ? &argc : &array[0];
  ptr[argc] = 1;
  ptr[1] = argc;
  assert(ptr[1] == argc);
  assert(array[1] == argc);
}
