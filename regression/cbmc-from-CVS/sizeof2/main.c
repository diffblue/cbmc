#include <assert.h>

long int f() {
  // sizeof is unsigned
  return (1 - sizeof(int)) >> 64;
}
              
int main()
{
  long int ret;

  ret=f();
  
  assert(ret==0);
}
