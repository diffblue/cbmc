
int main(int argc, char **argv)
{
  int i = 0;

  while(i < 10)
  {
    if(argc == 5)
      break;
    ++i;
    if(argc % 7)
      continue;
    argc--;
  }

  return argc;
}
