#include <assert.h>
#include <stdlib.h>

struct foo;

int main(int argc, char **argv)
{
  struct foo *thefoo = malloc(sizeof(struct foo));
  size_t s = sizeof(struct foo);
  assert(s == 0);
}
