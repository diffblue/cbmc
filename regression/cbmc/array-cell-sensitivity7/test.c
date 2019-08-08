#include <assert.h>
#include <stdlib.h>

int main(int argc, char **argv)
{
  int array[10];
  char *ptr = argc % 2 ? (char *)&array[0] : (char *)&argc;
  ptr[argc] = 'a';
  ptr[1] = (char)argc;
  assert(ptr[1] == (char)argc);
  assert(array[1] == (char)argc);
}
