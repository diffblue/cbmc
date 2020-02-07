#include <assert.h>
#include <string.h>

int main()
{
  char test[] = "foo";

  char *first_o = strchr(test, 'o');
  assert(*first_o == test[1]);
  assert(*first_o == test[0]);
  char *first_t = strchr(test, 't');
  assert(*first_t == test[1]);
  assert(*first_t == test[0]);
  return 0;
}
