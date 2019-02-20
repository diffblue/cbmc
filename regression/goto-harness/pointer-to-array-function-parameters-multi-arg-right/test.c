#include <assert.h>

int is_prefix_of(
  const char *string,
  int string_size,
  const char *prefix,
  int prefix_size)
{
  if(string_size < prefix_size)
  {
    return 0;
  }

  for(int ix = 0; ix < prefix_size; ++ix)
  {
    if(string[ix] != prefix[ix])
    {
      return 0;
    }
  }
  return 1;
}
