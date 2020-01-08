#include <assert.h>
#include <stdlib.h>

union foo;

int main(int argc, char **argv)
{
  size_t s = sizeof(union foo);
  assert(s == 0);
}
