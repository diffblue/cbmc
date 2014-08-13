#include <assert.h>

void f(int, int array[*][*]);

inline void f(int size, int array[size][++size])
{
  assert(size==1001);
  assert(sizeof(array)==sizeof(int *));
  assert(sizeof(*array)==sizeof(int)*1001);
}

int main()
{
  f(1000, 0);
}
