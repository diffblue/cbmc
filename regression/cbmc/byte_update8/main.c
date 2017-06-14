#include <assert.h>

int main()
{
  int x=0x01020304;
  short *p=((short*)&x)+1;
  *p=0xABCD;
  assert(x==0xABCD0304);
  p=(short*)(((char*)&x)+1);
  *p=0xABCD;
  assert(x==0xABABCD04);
}
