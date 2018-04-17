#include <assert.h>

#define ROUND_F(x) ((int)((x) + 0.5f))
int eight = ROUND_F(100.0f / 12.0f);

int main()
{
  assert(eight == 8);
}
