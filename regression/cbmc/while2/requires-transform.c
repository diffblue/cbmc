#include "assert.h"

int main()
{
  int count;

  do
  {
  } while(count < 5);

  while(count < 5)
    ;

  assert(count >= 5);
}
