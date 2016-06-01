int main()
{
  int input1, input2;
  
  if(input1 && input2)
  {
    // ok
  }
  
  if(!input1)
    input2=1;

  if(input1 && input2) // masked!
  {
  }
}
