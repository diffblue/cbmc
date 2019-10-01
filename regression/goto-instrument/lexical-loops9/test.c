
int main(int argc, char **argv)
{
  int i = 0;

  while(i < 10)
  {
    ++i;
    if(argc == 5)
    {
      ++i;
      break;
    }
    argc--;
  }

  return argc;
}
