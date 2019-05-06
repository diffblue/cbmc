#include "supp.h"
#include <assert.h>

const int five = 5;

int main()
{
  int ten = times_two(five);
  assert(ten == 10);
  return 0;
}
