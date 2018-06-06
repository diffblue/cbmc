#include <cassert>

void test_ref(int &x)
{
  x = 2;
}

void test_ptr(int *x)
{
  *x = 3;
}

int main (int argc, char *argv[])
{
  int x = 0;
  test_ref(x);
  assert(x==2);

  test_ptr(&x);
  assert(x==3);

  return 0;
}
