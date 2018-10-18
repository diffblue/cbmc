#include <assert.h>

int main(int argc, char** argv) {

  if(argc != 5)
    return 0;

  short x[argc];
  x[0]=0x0102;
  x[1]=0x0304;
  x[2]=0x0506;
  x[3]=0x0708;
  x[4]=0x090a;

  unsigned long long* alias=(unsigned long long*)(((char*)x)+0);
  *alias=0xf1f2f3f4f5f6f7f8;

  unsigned char* alias2=(unsigned char*)x;
  assert(alias2[0]==0xf8);
  assert(alias2[1]==0xf7);
  assert(alias2[2]==0xf6);
  assert(alias2[3]==0xf5);
  assert(alias2[4]==0xf4);
  assert(alias2[5]==0xf3);
  assert(alias2[6]==0xf2);
  assert(alias2[7]==0xf1);
  assert(alias2[8]==0x0a);
  assert(alias2[9]==0x09);

}
