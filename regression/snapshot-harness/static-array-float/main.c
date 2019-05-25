#include <assert.h>

float array[10];
float *iterator1;
float *iterator2;

void initialize()
{
  array[0] = 1.11;
  array[8] = 9.999;
  array[9] = 10.0;
  iterator1 = (float *)array;
  iterator2 = &array[9];
}

void checkpoint()
{
}

int main()
{
  initialize();
  checkpoint();

  assert(*iterator1 >= 1.10 && *iterator1 <= 1.12);
  assert(iterator1 != iterator2);
  assert(iterator2 == &array[9]);
  iterator2++;
  assert(*iterator2 == 0.0);

  return 0;
}
