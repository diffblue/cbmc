int main()
{
  unsigned char u=255;
  signed char *p;
  
  p=(signed char *)&u;
  
  assert(*p==-1);
}
