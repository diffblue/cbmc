char __CPROVER_mm_io_r(void *a, unsigned s)
{
  if((long)a==0x10)
    return 1;
  else if((long)a==0x11)
    return 2;
}

void __CPROVER_mm_io_w(void *a, unsigned s, char value)
{
  if((long)a==0x10)
    __CPROVER_assert(value==2, "correct value written");
}

int main()
{
  long i=0x10;
  char *p=(char *)i;
  unsigned char u = *(unsigned char *)i;
  char some_var=100;
  
  char z;
  z=p[1];
  __CPROVER_assert(z==2, "reading 0x11");
  
  // write
  p[0]=2;
  
  p=&some_var;
  z=p[0];
  __CPROVER_assert(z==100, "reading &some_var");
}

