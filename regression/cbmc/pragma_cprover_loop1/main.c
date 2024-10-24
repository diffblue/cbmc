int main()
{
#pragma CPROVER unwind 2
  for(int i = 0; i < 5; ++i)
  {
    if(i < 2)
      continue;

    for(int j = 0; j < 10; ++j)
      ++j;
  }

#pragma CPROVER unwind 1
  do
  {
    int x = 42;
  } while(0);

#pragma CPROVER unwind 10
  while(1)
  {
    int x = 42;
  }

  __CPROVER_assert(0, "false");
}
