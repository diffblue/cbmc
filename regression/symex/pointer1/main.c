int main()
{
  int *p, i;
  char *q;
  char ch0, ch1, ch2, ch3;

  // pointer into an integer
  q=(char *)&i;
  
  i=0x03020100;

  // endianness-dependent
  ch0=q[0];
  ch1=q[1];
  ch2=q[2];
  ch3=q[3];

  assert(ch0==0);
  assert(ch1==1);
  assert(ch2==2);
  assert(ch3==3);
  
  unsigned int *up=(unsigned int *)q;
  assert(*up==i);
}
