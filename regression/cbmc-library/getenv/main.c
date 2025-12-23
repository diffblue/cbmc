#include <stdlib.h>

int main()
{
  char *something;
  // there should not be any overflow in there
  something = getenv("HOME");
  if(something != NULL)
    return something[0];
  else
    return 0;
}
