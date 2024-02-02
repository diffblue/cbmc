#include <assert.h>

int main(int argc, char* argv[])
{
  if(argc>=2)
  {
    assert(argv[1]!=0);
    // we can access at least one character (might be a string-terminating zero)
    char first_char = *argv[1];
  }

  return 0;
}
