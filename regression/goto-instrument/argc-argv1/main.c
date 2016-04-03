#include <assert.h>

int main(int argc, char* argv[])
{
  if(argc>=2)
    assert(argv[1]!=0);

  return 0;
}
