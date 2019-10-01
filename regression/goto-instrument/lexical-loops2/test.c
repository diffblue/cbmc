
int main(int argc, char **argv)
{
  int i = 0;

  while(i < 10)
  {
    ++i;
    argc--;
  }

  return argc;
}
