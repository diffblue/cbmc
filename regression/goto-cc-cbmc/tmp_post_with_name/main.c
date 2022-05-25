#include <assert.h>

int main(int argc, char **argv)
{
  char *ptr;
  ptr = malloc(2);
  ptr += 2;
  char c = *ptr++;
  return 0;
}
