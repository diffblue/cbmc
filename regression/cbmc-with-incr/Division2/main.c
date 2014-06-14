_Bool nondet_bool();

void main()
{
  int i=2, j;
  
  if(nondet_bool())
    i++;

  j=(i/=2);

  assert(i==1);
  assert(j==1);
}
