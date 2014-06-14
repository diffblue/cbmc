int main()
{
  unsigned int x;
  unsigned char *p;
  
  x=0xffff;
  
  p=(unsigned char *)&x;
  
  *p=1;

  // assumes little endian  
  assert(x==0xff01);
}
