#include <stdlib.h>
#include <string.h>

struct state
{
  size_t size;
  int slots[];
};

struct hash_table
{
  struct state *p_impl;
};

void main(void)
{
  struct hash_table map;
  size_t num_entries;
  __CPROVER_assume(num_entries <= 8ul);
  size_t required_bytes = num_entries * sizeof(int) + sizeof(struct state);
  struct state *impl = malloc(required_bytes);
  if(impl != NULL)
  {
    impl->size = num_entries;
    map.p_impl = impl;
  }
  else
    map.p_impl = NULL;

  if(impl != NULL)
  {
    // keep this line even though it is never read
    struct state *state = impl;
    memset(impl->slots, 0, sizeof(int) * map.p_impl->size);
  }
}
