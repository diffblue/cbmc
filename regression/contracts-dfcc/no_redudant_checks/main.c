#include <stdlib.h>
const int N = 100;
int main()
{
  int *buf = malloc(N * sizeof(*buf));
  char *lb = (((char *)buf) - __CPROVER_POINTER_OFFSET(buf));
  char *ub = (((char *)buf) - __CPROVER_POINTER_OFFSET(buf)) +
             __CPROVER_OBJECT_SIZE(buf) - 1;
}
