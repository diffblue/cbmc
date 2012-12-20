_Bool nondet_bool();

void main()
{
  int i=2;
  
  if(nondet_bool())
    i++;

  i/=2;
  assert(i==1);
}
