int main()
{
  int i = 0;
  int count;
  __CPROVER_assume(count > 10);

  if(count % 2)
    goto head2;

head:
  count--;
head2:
  ++i;
  if(i < 10)
    goto head;

  return count;
}
