#include <assert.h>

typedef struct stritem
{
  unsigned nkey;
  unsigned cas[];
} item;

int foo(item *it)
{
  assert(it->cas[0] == 0);
  return 0;
}
