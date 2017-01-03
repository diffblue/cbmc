unsigned char* init()
{
  unsigned long buffer_size;
  if(buffer_size!=1) return 0;

  unsigned char* buffer=__CPROVER_allocate(buffer_size, 0);
  __CPROVER_assert(buffer!=0, "malloc did not return NULL");

  buffer[0]=10;

  return buffer;
}

int main()
{
  unsigned char* ret=init();

  if(ret!=0)
  {
    unsigned char r=ret[0];
    __CPROVER_assert(r==10, "ret[0] is 10");
  }

  return 0;
}
