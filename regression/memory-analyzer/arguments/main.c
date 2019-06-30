#include <string.h>

void checkpoint()
{
}

int x = 0;

int main(int argc, char *argv[])
{
  if(argc == 3 &&
    strcmp(argv[1], "abc") == 0 &&
    strcmp(argv[2], "xyz") == 0)
  {
    x = 1;
  }

  checkpoint();

  return 0;
}
