#include <assert.h>

int main(int argc, char** argv) {

  if(argc != 10)
    return 0;

  unsigned char x[argc];
  x[0]=0x01;
  x[1]=0x02;
  x[2]=0x03;
  x[3]=0x04;
  x[4]=0x05;
  x[5]=0x06;
  x[6]=0x07;
  x[7]=0x08;
  x[8]=0x09;
  x[9]=0x0a;

  unsigned long long* alias=(unsigned long long*)(((char*)x)+1);
  *alias=0xf1f2f3f4f5f6f7f8;

  unsigned char* alias2=(unsigned char*)x;
  assert(alias2[0]==0x01);
  assert(alias2[1]==0xf8);
  assert(alias2[2]==0xf7);
  assert(alias2[3]==0xf6);
  assert(alias2[4]==0xf5);
  assert(alias2[5]==0xf4);
  assert(alias2[6]==0xf3);
  assert(alias2[7]==0xf2);
  assert(alias2[8]==0xf1);
  assert(alias2[9]==0x0a);

}
