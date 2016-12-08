int main()
{
  int input1, input2;

  __CPROVER_input("input1", input1);
  __CPROVER_input("input2", input2);

  if(input1 && input2)
  {
  }
  else if(input1)
  {
  }
  else if(input2)
  {
    if(input1) // can't be true
    {
    }
  }
}
