// A pointer stored in a struct that is an element of an array with more than
// the default 64 elements.  Field sensitivity is not applied to that array,
// so CBMC should say so rather than silently lose precision.
static unsigned short storage[4];

struct ring
{
  unsigned short *free_ids;
  int type;
};

#ifndef N_RINGS
#  define N_RINGS 65
#endif

struct adapter
{
  struct ring rings[N_RINGS];
};

static struct adapter adapter;

static char scalar_buffer[4096]; // must not be reported

int main(void)
{
  unsigned k;
  adapter.rings[0].free_ids = storage;
  adapter.rings[0].type = 1;
  for(unsigned i = 0; i < 4; i++)
    adapter.rings[0].free_ids[i] = (unsigned short)i;
  if(k < 4096)
    scalar_buffer[k] = 1;
  __CPROVER_assert(adapter.rings[0].type == 1, "type survives");
  return 0;
}
