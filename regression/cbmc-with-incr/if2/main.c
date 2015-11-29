int nondet_int();

int main()
{
  int i, j, k;
  
  i=nondet_int();
  k=nondet_int();
  
  if(i)
  {
  }
  else
  {
    if(k)
    {
      assert(0);
    }
  }
}
