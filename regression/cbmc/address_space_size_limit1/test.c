
#include <stdlib.h>
#include <assert.h>

int main(int argc, char** argv)
{

  int i;
  char* c;
  for(i=0; i<300; ++i)
  {
    c=(char*)malloc(1);
    assert(c!=(char*)0);
  }

}
