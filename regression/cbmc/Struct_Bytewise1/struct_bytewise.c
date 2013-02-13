// Determine endianness.
// Follows http://wiki.debian.org/ArchitectureSpecificsMemo

#if defined(__avr32__) || defined(__hppa__)    || defined(__mk68k__) || \
    defined(__mips__)  || defined(__powerpc__) || defined(__s390__) || \
    defined(__s390x__) || defined(__sparc__)

#define BIG_ENDIAN

#endif

typedef struct my_struct
{
  // we hope these are 32 bit each on all architectures
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

  #ifdef BIG_ENDIAN
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
 
