int main()
{
  unsigned int i;
  i=0;
  
  float *p;
  p=(float *)&i;
  
  float f=*p;
  
  assert(f==0.0);
}
