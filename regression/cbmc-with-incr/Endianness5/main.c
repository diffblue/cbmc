unsigned char  regb[100];
unsigned short *ptrUShort;
unsigned short shortTmp;

int main()
{
  ptrUShort = (unsigned short*)(&regb[12]);
  shortTmp= *ptrUShort; 

  // should pass
  *ptrUShort = 1234;   
}
