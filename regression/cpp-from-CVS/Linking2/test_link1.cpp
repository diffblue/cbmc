#include <assert.h>

extern int x;
extern int f(void);

int main()
{
  int z;
  
  x=z;
  assert(f()==z);
}
