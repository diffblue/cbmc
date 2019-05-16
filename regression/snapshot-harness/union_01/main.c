#include <assert.h>

union Un {
  int i;
  float f;
} un;

int *ip;
float *fp;

void initialize()
{
  un.i = 1;
  ip = &un.i;
  fp = &un.f;
}

void checkpoint()
{
}

int main()
{
  initialize();
  checkpoint();

  assert(ip == &un.i);
  assert(*ip == un.i);
  *fp = 2.0f;
  assert(un.f == 2.0f);
}
