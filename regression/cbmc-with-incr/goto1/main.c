int main()
{
  int i, j;
  
  if(i)
    goto l;
    
  if(j)
    goto l;
    
  assert(!i && !j);
 
 l:; 
}
