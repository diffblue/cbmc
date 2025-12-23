#include <assert.h>
#include <stdio.h>

int main()
{
  FILE *f = fdopen(0, "r");
  if(!f)
    return 1;

  char buffer[3];
  size_t result = fread(buffer, 3, 1, f);
  assert(result <= 3);

  fclose(f);

  return 0;
}
