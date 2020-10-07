#include <stdlib.h>

int main(void)
{
  void *ptr = malloc(sizeof(char));
  if(ptr == NULL)
    return 0;

  void *ptr1 = realloc(ptr, 2 * sizeof(char));
  if(ptr1 == NULL)
  {
    free(ptr);
    return 0;
  }

  free(ptr1);
}
