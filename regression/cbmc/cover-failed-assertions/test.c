#include <stdlib.h>

int main()
{
  int *ptr = malloc(sizeof(*ptr));
  int a;

  // pointer check would detect the dereference of a null pointer here
  // default --cover lines behaviour is to treat non-cover assertions as
  // assumptions instead, so in the ptr == NULL case we don't get past this line
  // leading to failed coverage for the body of the if statement down below
  a = *ptr;

  if(ptr == NULL)
    a = 1;

  return 0;
}
