#include <assert.h>
#include <stdio.h>

int main()
{
  char buffer[3] = {'a', 'b', '\0'};
  FILE *f = fdopen(0, "r");
  if(!f)
    return 1;

  char *p = fgets(buffer, 3, f);
  if(p)
  {
    assert(buffer[1] == p[1]);
    assert(buffer[2] == '\0');
    assert(p[1] == 'b'); // expected to fail
  }

  fclose(f);

  return 0;
}
