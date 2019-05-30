#include <assert.h>

int array[10];
int *iterator1;
int *iterator2;

void initialize()
{
  array[0] = 1;
  array[8] = 9;
  array[9] = 10;
  iterator1 = (int *)array;
  iterator2 = &array[9];
}

void checkpoint()
{
}

int main()
{
  initialize();
  checkpoint();

  assert(*iterator1 == 1);
  assert(iterator1 != iterator2);
  assert(iterator2 == &array[9]);
  iterator2++;
  assert(*iterator2 == 0);

  return 0;
}
