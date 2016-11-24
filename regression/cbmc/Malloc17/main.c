unsigned char* init1()
{
  unsigned long size;
  if (size!=1) return 0;

  assert(sizeof(unsigned char)==1);
  unsigned char* buffer=__CPROVER_malloc(1);
  assert(buffer!=0);

  buffer[0]=0;

  return buffer;
}

unsigned char* init2()
{
  unsigned long size;
  if (size!=1) return 0;

  assert(sizeof(unsigned char)==1);
  unsigned char* buffer=__CPROVER_malloc(1*sizeof(unsigned char));
  assert(buffer!=0);

  buffer[0]=0;

  return buffer;
}

unsigned char* init3()
{
  unsigned long size;
  if (size!=1) return 0;

  assert(sizeof(unsigned char)==1);
  unsigned char* buffer=__CPROVER_malloc(sizeof(unsigned char)*1);
  assert(buffer!=0);

  buffer[0]=0;

  return buffer;
}

int main()
{
  unsigned char* ret1=init1();

  if(ret1!=0)
  {
    unsigned char r1=ret1[0];
    assert(r1==0);
  }

  unsigned char* ret2=init2();

  if(ret2!=0)
  {
    unsigned char r2=ret2[0];
    assert(r2==0);
  }

  unsigned char* ret3=init3();

  if(ret3!=0)
  {
    unsigned char r3=ret3[0];
    assert(r3==0);
  }

  return 0;
}

