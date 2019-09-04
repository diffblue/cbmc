int main(int argc, char **argv)
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

  i = 0;
top2:
{
  ++i;
  if(i == 5)
    goto top2;
  ++i;
}
  if(i < 10)
    goto top2;
}
