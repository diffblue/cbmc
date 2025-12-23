#include <assert.h>
#include <string.h>

int main()
{
  char A1[5] = {'a', 'b', '\0'};
  char B1[3] = {'c', 'd', '\0'};

  strcat(A1, B1);
  assert(A1[3] == 'd');
  assert(strlen(A1) == 4);

  return 0;
}
