int main()
{
  int count;
  __CPROVER_assume(count > 0);
loop_header:
  --count;
  if(count == 1)
    goto loop_header;
  else if(count == 2)
    goto loop_header;
  return count;
}
