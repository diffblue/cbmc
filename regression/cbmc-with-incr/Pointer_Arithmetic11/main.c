int main()
{
  int i, ii;
  int data=0;
  char *p=(char *)&data;
  i=ii;
  
  __CPROVER_assume(i>=0 && i<4);
  
  p[i]++;

  if(i==0)
    assert(data==1);
  else if(i==1)
    assert(data==0x100);
  else if(i==2)
    assert(data==0x10000);
  else
    assert(data==0x1000000);
}
