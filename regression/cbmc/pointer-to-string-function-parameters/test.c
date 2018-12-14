#include <assert.h>
#include <stddef.h>
#include <string.h>

int test(char *string, size_t size)
{
  for(size_t ix = 0; ix + 1 < size; ++ix)
  {
    char c = string[ix];
    // characters except the last should fall in printable range
    assert(c == '\n' | c == '\r' | c == '\t' | (c >= 32 && c <= 126));
  }
  assert(strlen(string) + 1 == size);
}
