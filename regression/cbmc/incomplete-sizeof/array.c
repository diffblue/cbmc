#include <assert.h>
#include <stdlib.h>

int arr[];

int main(int argc, char **argv)
{
  size_t s = sizeof(arr);
  assert(s == 4);
}
