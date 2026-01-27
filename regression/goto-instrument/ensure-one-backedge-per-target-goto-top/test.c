int main()
{
  int i = 0;
top:
{
  ++i;
  if(i == 5)
    goto top;
  ++i;
}
  if(i < 10)
    goto top;
}
