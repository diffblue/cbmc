#include <assert.h>
#include <stdlib.h>

enum foo;

int main(int argc, char **argv)
{
  size_t s = sizeof(enum foo);
  assert(s == 0);
}
