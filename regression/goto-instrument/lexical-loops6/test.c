
int main(int argc, char **argv)
{
  int i = 0;

  if(argc % 2)
    goto head2;

head:
  argc--;
head2:
  ++i;
  if(i < 10)
    goto head;

  return argc;
}
