#include <assert.h>
#include <string.h>

struct conft
{
  _Bool red;
  int one;
};

int main()
{
  struct conft conf_init = {0, 1};
  struct conft my_conf;
  memcpy((char *)&my_conf, (char *)&conf_init, sizeof(struct conft));
  int num = my_conf.one;
  assert(num == 1);
  return 0;
}
