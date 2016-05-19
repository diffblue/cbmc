int main()
{
  int input1, input2;

  __CPROVER_cover(input1);
  __CPROVER_cover(!input1);
  
  if(input1)
  {
    __CPROVER_cover(!input1); // won't work
  }
}
