#include <stdlib.h>

struct record
{
  int key;
  int values[4];
};

int main()
{
  struct record *r = malloc(sizeof(struct record));
  if(!r)
    return 0;
  r->key = 1;
  __CPROVER_assert(r->key == 1, "key");
  __CPROVER_assert(0, "WRONG (must FAIL)");
  return 0;
}
