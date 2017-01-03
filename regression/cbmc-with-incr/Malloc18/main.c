unsigned char* init()
{
  unsigned long size;
  if (size!=1) return 0;

  assert(sizeof(unsigned char)==1);
  unsigned char* buffer=__CPROVER_allocate(size, 0);
  assert(buffer!=0);

  buffer[0]=0;

  return buffer;
}

int main()
{
  unsigned char* ret=init();

  if(ret!=0)
  {
    unsigned char r=ret[0];
    assert(r==0);
  }

  return 0;
}
