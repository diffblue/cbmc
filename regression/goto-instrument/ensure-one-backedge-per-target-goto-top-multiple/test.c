int main(int argc, char **argv)
{
  int i = 0;
top:
{
  ++i;
  if(i == 5)
    goto top;
  if(i == 6)
    goto top;
  if(i == 7)
    goto top;
  if(i == 8)
    goto top;
  ++i;
}
  if(i < 10)
    goto top;
}
