#include <assert.h>
#include <string.h>

int main()
{
  int i;
  char *test = i ? "fo\0tis" : "notfoti";

  char *first_o = strchr(test, 'o');
  assert(first_o != NULL);
  assert(*first_o == test[0]);
  return 0;
}
