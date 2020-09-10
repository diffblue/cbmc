#include "assert.h"

int main()
{
  int count = 0;
  do
  {
    count = count + 1;
  } while(count < 5);

  do
  {
  } while(count < 5);

  while(count < 5)
    ;

  assert(count == 5);
  assert(count == 17);
}
