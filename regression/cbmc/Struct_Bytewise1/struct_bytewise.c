typedef struct my_struct
{
  unsigned long a;
  unsigned long b;
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

  // this is little endian
  assert(arrayTmp[0]==1);
  assert(arrayTmp[1]==0);
  assert(arrayTmp[2]==0);
  assert(arrayTmp[3]==0);
  assert(arrayTmp[4]==2);
  assert(arrayTmp[5]==0);
  assert(arrayTmp[6]==0);
  assert(arrayTmp[7]==1);
}
 
