#include <assert.h>

int array2[10]={ 2 };
extern int array1[];

void check2(void)
{
//  assert(sizeof(array1)==sizeof(void *));
  assert(sizeof(array2)==sizeof(int)*10);
  assert(array1[0]==1);
  assert(array2[0]==2);
}
