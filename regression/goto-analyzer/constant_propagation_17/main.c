#include <assert.h>

int main()
{
  int i=0, j=2;

  while(i < 50)
  {
    i++;
    j++;
  }
  __CPROVER_assert(i < 51, "i<51");
}

