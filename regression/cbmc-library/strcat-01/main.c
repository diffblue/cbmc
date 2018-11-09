#include <assert.h>
#include <string.h>

int main()
{
  char A1[5] = {'a', 'b', '\0'};
  char B1[3] = {'c', 'd', '\0'};

  strcat(A1, B1);
  assert(A1[3] == 'd');
  assert(strlen(A1) == 4);

  char A2[5] = {'a', 'b', '\0'};
  char B2[3] = {'c', 'd', '\0'};

  strncat(A2, B2, 2);
  assert(A2[3] == 'd');
  assert(strlen(A2) == 4);

  char A3[5] = {'a', 'b', '\0'};
  char B3[3] = {'c', 'd', '\0'};

  strncat(A3, B3, 1);
  assert(A3[3] == '\0');
  assert(strlen(A3) == 4); // expected to fail

  return 0;
}
