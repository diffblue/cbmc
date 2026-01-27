int main()
{
  int i = 0;
  int count;
  __CPROVER_assume(count > 10);

head:
  count--;
  ++i;
  if(i < 10 && i % 2)
    goto head;
  else if(i < 10)
    goto head;

  return count;
}
