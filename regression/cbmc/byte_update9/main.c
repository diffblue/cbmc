#include <assert.h>

int main()
{
  int x=0x01020304;
  short *p=((short*)&x)+1;
  *p=0xABCD;
  assert(x==0x0102ABCD);
  p=(short*)(((char*)&x)+1);
  *p=0xABCD;
  assert(x==0x01ABCDCD);
}
