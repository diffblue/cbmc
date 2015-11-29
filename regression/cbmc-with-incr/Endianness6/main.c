#include <stdio.h>

int main()
{
  int *i_p;
  char c_array[10];
  
  i_p=(int *)c_array;
  *i_p=0x01020304;
  
  // big-endian
  assert(c_array[0]==1 &&
         c_array[1]==2 &&
         c_array[2]==3 &&
         c_array[3]==4);
  
  char *c_p;
  int i=0x01020304;
  
  c_p=(char *)&i;
  
  // big-endian
  assert(c_p[0]==1 &&
         c_p[1]==2 &&
         c_p[2]==3 &&
         c_p[3]==4);
}
