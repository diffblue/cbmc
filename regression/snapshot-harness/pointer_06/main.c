#include <assert.h>
#include <malloc.h>

int *p;
int *q;

void initialize()
{
  p = malloc(sizeof(int));
  q = p;
}

void checkpoint()
{
}

int main()
{
  initialize();
  checkpoint();

  assert(p == q);
}
