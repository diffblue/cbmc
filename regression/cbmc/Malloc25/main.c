#include <stdlib.h>

int main(int argc, char *argv[])
{
  int *p = malloc((size_t)argc * (size_t)argc * sizeof(int));
  return 0;
}
