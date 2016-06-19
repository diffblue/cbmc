#include <assert.h>

int asd();

int main()
{
  int v1=asd(), v2=asd();
  assert(v1==v2);
}
