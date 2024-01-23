#include <assert.h>

int main()
{
  int x = 0;

  do
  {
    do
    {
      x++;
    } while(0);
  } while(0);

  assert(x <= 10);
}
