#include <new>

struct P
{
  int x;
};

int main()
{
  alignas(P) unsigned char buffer[3 * sizeof(P)];
  P *p = new(buffer) P[3];
  p[2].x = 42;
  __CPROVER_assert((void *)p == (void *)buffer, "placement new[] address");
  __CPROVER_assert(((P *)buffer)[2].x == 42, "placement new[] storage");
  return 0;
}
