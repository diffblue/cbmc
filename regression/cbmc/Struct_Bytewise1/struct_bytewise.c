typedef struct my_struct
{
  // We hope these are 32 bit each on all architectures,
  // and that there is no padding between them.
  unsigned a;
  unsigned b;
} t_logAppl;

static t_logAppl logAppl;
static unsigned char arrayTmp[8];

void CopyBuffer(unsigned char *src) {
  int i;
  for(i=0;i<8;i++){
    arrayTmp[i] = src[i];
  }
}

int main()
{
  logAppl.a=1;
  logAppl.b=0x01000002;
  CopyBuffer((unsigned char *)&logAppl);

#if defined(__BYTE_ORDER__) && __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
  assert(arrayTmp[0]==0);
  assert(arrayTmp[1]==0);
  assert(arrayTmp[2]==0);
  assert(arrayTmp[3]==1);

  assert(arrayTmp[4]==1);
  assert(arrayTmp[5]==0);
  assert(arrayTmp[6]==0);
  assert(arrayTmp[7]==2);
  #else
  // this is little endian
  assert(arrayTmp[0]==1);
  assert(arrayTmp[1]==0);
  assert(arrayTmp[2]==0);
  assert(arrayTmp[3]==0);

  assert(arrayTmp[4]==2);
  assert(arrayTmp[5]==0);
  assert(arrayTmp[6]==0);
  assert(arrayTmp[7]==1);
  #endif
}
