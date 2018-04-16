#include <assert.h>

void will_not_return(void);

int main(void)
{
  will_not_return();
  assert(0);
}
