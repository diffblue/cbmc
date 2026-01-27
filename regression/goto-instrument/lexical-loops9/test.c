int main()
{
  int i = 0;
  int count;
  __CPROVER_assume(count > 5);

  while(i < 10)
  {
    ++i;
    if(count == 5)
    {
      ++i;
      break;
    }
    count--;
  }

  return count;
}
