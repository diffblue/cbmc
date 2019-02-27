#include <assert.h>

int stringlength(char *s)
{
  int counter = 0;
  while(*s++ != 0)
    counter++;
  return counter;
}

void calling_func(char *s, int length)
{
  // WRONG: This should be stringlength(s)
  // +1 because length is going to be length
  // of the array, not the string
  assert(stringlength(s) == length);
}
