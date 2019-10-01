
int main(int argc, char **argv)
{
  int i = 0;

  do
  {
    ++i;
    argc--;
  } while(i < 10);

  return argc;
}
