int main()
{
  int i, j;

  i=1;

  if(j)
    goto l;

  i=2;
 
 l:; 
 
  assert(i==1 || !j);
}
