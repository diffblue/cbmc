#include <assert.h>
#include <malloc.h>

int *array;
int *iterator1;
int *iterator2;
int *iterator3;

void initialize()
{
  array = (int *)malloc(sizeof(int) * 10);
  array[0] = 1;
  array[1] = 2;
  array[2] = 3;
  array[3] = 4;
  array[4] = 5;
  array[5] = 6;
  array[6] = 7;
  array[7] = 8;
  array[8] = 9;
  array[9] = 10;
  iterator1 = (int *)array;
  iterator2 = &array[1];
  iterator3 = array + 1;
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
  assert(iterator2 == iterator3);
  assert(iterator2 == &array[1]);
  assert(*iterator3 == array[1]);
  assert(*iterator3 == 2);
  iterator3 = &array[9];
  iterator3++;
  assert(*iterator3 == 0);

  return 0;
}
