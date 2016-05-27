int main()
{
  int input1, input2;

  __CPROVER_assert(!input1, "");
  
  if(input1)
  {
    __CPROVER_assert(!input1, ""); // will work, we ignore the assertion
  }
}
