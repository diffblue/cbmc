#include <assert.h>

int x;

int f()
{
  if(x)
    return 1;
  else
    return 2;

  return 3;
}

int main()
{
  int y;
  y = f(); 
}

