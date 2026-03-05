int main()
{
  int i = 0;
  int count;
  __CPROVER_assume(count > 10);

  while(i < 10)
  {
    ++i;
    count--;
  }

  return count;
}
