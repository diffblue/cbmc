#include <assert.h>
#include <malloc.h>

int a;
int *a1;
int *iterator1;
int *a2;
int *a3;
int *iterator2;
int *a4;
int *a5;
int *iterator3;
int *a6;
int *a7;
int *array2;
int *a8;

void initialize()
{
  array2 = (int *)malloc(sizeof(int) * 10);
  array2[0] = 1;
  array2[1] = 2;
  array2[2] = 3;
  array2[3] = 4;
  array2[4] = 5;
  array2[5] = 6;
  array2[6] = 7;
  array2[7] = 8;
  array2[8] = 9;
  array2[9] = 10;
  iterator1 = (int *)array2;
  iterator2 = &array2[1];
  iterator3 = array2 + 1;
  a1 = &a;
  a2 = a1;
  a3 = a2;
  a4 = a3;
  a5 = a4;
  a6 = a5;
  a7 = a6;
  a8 = a7;
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
  assert(iterator2 == &array2[1]);
  assert(*iterator3 == array2[1]);
  assert(*iterator3 == 2);
  iterator3 = &array2[9];
  iterator3++;
  assert(*iterator3 == 0);

  return 0;
}
