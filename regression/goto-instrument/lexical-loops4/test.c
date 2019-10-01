
int main(int argc, char **argv)
{
  int i = 0;

head:
  ++i;
  argc--;
  if(i < 10)
    goto head;

  return argc;
}
