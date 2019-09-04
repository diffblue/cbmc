int main(int argc, char **argv)
{
  int i = 0;
top:
{
  ++i;
  if(i == 5)
    goto top;
  if(i > 10)
    return 0;
  ++i;
}
  goto top;
}
