#include <assert.h>
#include <stddef.h>

int is_prefix_of(
  const char *string,
  size_t string_size,
  const char *prefix,
  size_t prefix_size)
{
  if(string_size < prefix_size)
  {
    return 0;
  }
  assert(prefix_size <= string_size);
  // oh no! we should have used prefix_size here
  for(int ix = 0; ix < string_size; ++ix)
  {
    if(string[ix] != prefix[ix])
    {
      return 0;
    }
  }
  return 1;
}
