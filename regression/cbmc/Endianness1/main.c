int main()
{
  unsigned int u=1;
  unsigned char *p;
  unsigned char x, y;
  
  p=(unsigned char *)&u;

  x=*p;

  // works only on little endian
  assert(x==1);

  y=p[1];

  assert(y==0);
}
