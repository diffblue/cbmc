#include <assert.h>

int array1[2][2] = {
  {1, 2},
  {3, 4}
};

int array2[]={ [1]=10, [2]=20, [3]=30, [10]=100 };

extern int array3[8];
int array3[]={ 1, 2, 3, 4, 5, 6, 7, 8 };

int array4[2] = { [1] 42 };
int array5[2][2] = { { 42, 42 }, {[1] 42 } };
int array6[2][2] = { [1] {[1] 42 } };

int main(void)
{
  assert(array1[0][1] ==2);
  assert(array1[1][0] ==3);    // returned false in this case
  
  assert(array2[0]==0);
  assert(array2[1]==10);
  assert(array2[10]==100);
  assert(sizeof(array2)==sizeof(int)*11);
  
  assert(sizeof(array3)==sizeof(int)*8);
  
  return 0;
}
