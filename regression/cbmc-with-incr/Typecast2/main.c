#include <assert.h>

int main()
{
  unsigned int i=2;
  assert(0l==(signed long int)(i - (unsigned int)2));
  return 0;
}
