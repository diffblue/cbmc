#include <assert.h>
#include <stdio.h>

int asprintf(char **ptr, const char *fmt, ...);

int main()
{
  char *result = NULL;
  int bytes = asprintf(&result, "%d\n", 42);
  if(bytes != -1)
  {
    assert(result[bytes] == 0);
    free(result);
  }
  return 0;
}
