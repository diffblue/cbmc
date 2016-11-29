int main()
{
  int input1, input2, input3;

  __CPROVER_input("input1", input1);
  __CPROVER_input("input2", input2);
  __CPROVER_input("input3", input3);

  if(input1 && input2 && input3)
  {
  }
  else
  {
  }
}
