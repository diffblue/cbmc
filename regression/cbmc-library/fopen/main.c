#include <stdio.h>

int main()
{
  FILE *f = fopen("some_file", "r");
  if(!f)
    return 1;

  // fopen returns NULL or some pointer that is safe to dereference
  (void)*f;

  return 0;
}
