int main()
{
  int i = 0;
  int count;
  __CPROVER_assume(count > 10);

  do
  {
    ++i;
    count--;
  } while(i < 10);

  return count;
}
