#include <assert.h>

int array1[10]={ 1 };
extern int array2[];

void check1(void)
{
  assert(sizeof(array1)==sizeof(int)*10);
//  assert(sizeof(array2)==sizeof(void *));
  assert(array1[0]==1);
  assert(array2[0]==2);
}

void check2(void);

int main()
{
  check1();
  check2();
}
