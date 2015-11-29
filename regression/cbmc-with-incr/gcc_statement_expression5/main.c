#include <assert.h>

int main()
{
  char array[40];

  // arrays turn into pointers
  assert(sizeof(({ array; }))==sizeof(char *));
  assert(sizeof(array)==40);

  // but it's not promotion
  assert(sizeof(({ (char)1; }))==sizeof(char));
}
