int main()
{
  int i;
  
  i=0;

loop:
  assert(i<10);
  i++;
  
  if(i<10)
    goto loop;
  
  assert(i==10);
}
