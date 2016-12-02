int main()
{
  int input1;
  int x=0;

  __CPROVER_input("input1", input1);

  if(input1)
  {
    x=1;
  }

  if(input1 && !x)
  {
    x=2; // I am dead!
  }
}
