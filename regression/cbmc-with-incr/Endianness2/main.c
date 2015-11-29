int main()
{
  unsigned int u=1;
  unsigned char *p;
  unsigned char x, y;
  
  p=(unsigned char *)&u;

  x=*p;

  // works only on big endian
  assert(x==0);

  y=p[3];

  assert(y==1);
}
