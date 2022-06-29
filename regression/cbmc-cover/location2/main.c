#include <string.h>

#define BUFLEN 100

static void *(*const volatile memset_func)(void *, int, size_t) = memset;

int main()
{
  char buffer[BUFLEN];
  memset_func(&buffer, 0, BUFLEN);
}
