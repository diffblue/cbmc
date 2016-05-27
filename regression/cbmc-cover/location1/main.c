int main()
{
  int input1;
  int x=0;
  
  if(input1)
  {
    x=1;
  }

  if(input1 && !x)
  {
    x=2; // I am dead!
  }
}
