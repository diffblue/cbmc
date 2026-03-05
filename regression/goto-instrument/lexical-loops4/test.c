int main()
{
  int i = 0;
  int count;
  __CPROVER_assume(count > 10);

head:
  ++i;
  count--;
  if(i < 10)
    goto head;

  return count;
}
