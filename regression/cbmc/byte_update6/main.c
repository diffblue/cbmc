#include <stdio.h>
#include <assert.h>

int main(int argc, char** argv) {

  if(argc != 2)
    return 0;

  unsigned long long x[argc];
  x[0]=0x0102030405060708;
  x[1]=0x1112131415161718;

  unsigned short* alias=(unsigned short*)(((char*)x)+8);
  *alias=0xedcb;

  unsigned char* alias2=(unsigned char*)x;
  /*
  for(int i = 0; i < 16; ++i)
    printf("%02hhx\n",alias2[i]);
  */

  assert(alias2[0]==0x08);
  assert(alias2[1]==0x07);
  assert(alias2[2]==0x06);
  assert(alias2[3]==0x05);
  assert(alias2[4]==0x04);
  assert(alias2[5]==0x03);
  assert(alias2[6]==0x02);
  assert(alias2[7]==0x01);
  assert(alias2[8]==0xcb);
  assert(alias2[9]==0xed);
  assert(alias2[10]==0x16);
  assert(alias2[11]==0x15);
  assert(alias2[12]==0x14);
  assert(alias2[13]==0x13);
  assert(alias2[14]==0x12);
  assert(alias2[15]==0x11);

}
