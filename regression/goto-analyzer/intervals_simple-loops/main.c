#include <assert.h>
const int g_N = 2;

void main(void)
{
  for(int i = 0; i < g_N; i++)
  {
    assert(0);
  }

  for(int j = 4; j >= g_N; j--)
  {
    assert(0);
  }
}
