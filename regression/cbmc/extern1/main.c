#include <stdio.h>
#include <assert.h>

int some_global = 10;

void shadow()
{
  int some_global = 5;

  printf("local: %d\n", some_global);
  {
    int some_global = 0;
    ++some_global;
    printf("local2: %d\n", some_global);
  }

  printf("local: %d\n", some_global);
  {
    extern int some_global;
    ++some_global;
    printf("global: %d\n", some_global);
    assert(some_global == 11);
  }

  assert(some_global == 5);
}

int main(void)
{
  shadow();
}
