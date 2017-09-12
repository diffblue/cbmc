int main()
{
  int input1, input2;

  __CPROVER_input("input1", input1);
  __CPROVER_input("input2", input2);

  // assert() is platform-dependent and changes set of coverage goals
  __CPROVER_assert(!input1, "");

  if(input1)
  {
    __CPROVER_assert(!input1, ""); // will work, we ignore the assertion
  }
}
