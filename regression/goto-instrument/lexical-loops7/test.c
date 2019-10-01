
int main(int argc, char **argv)
{
  int i = 0;

head:
  argc--;
  ++i;
  if(i < 10 && i % 2)
    goto head;
  else if(i < 10)
    goto head;

  return argc;
}
