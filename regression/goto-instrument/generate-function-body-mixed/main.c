#include <assert.h>

void generate_me();

void already_has_body()
{
  assert(0);
}

int main(void)
{
  generate_me();
  already_has_body();
  return 0;
}
