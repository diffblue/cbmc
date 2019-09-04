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
}
