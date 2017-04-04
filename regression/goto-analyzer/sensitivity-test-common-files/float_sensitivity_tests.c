#include <assert.h>

int main(int argc, char *argv[])
{
  // Test if we can represent constant floats
  float x=0.0;
  assert(x==0.0);
  assert(x==1.0);
  return 0;
}
