int main()
{
  int input1, input2;

  __CPROVER_input("input1", input1);
  __CPROVER_input("input2", input2);

  __CPROVER_cover(input1);
  __CPROVER_cover(!input1);

  if(input1)
  {
    __CPROVER_cover(!input1); // won't work
  }

  // should not produce a goal
  __CPROVER_assert(input1, "");
}
