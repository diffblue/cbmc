#include <assert.h>

int plus(int i)
{
  return i + 1;
}

int minus(int i)
{
  return i - 1;
}

int (*fun_ptr1)(int);
int (*fun_ptr2)(int);

void initialize()
{
  fun_ptr1 = &plus;
  fun_ptr2 = &minus;
}

void checkpoint()
{
}

int main()
{
  initialize();
  checkpoint();

  assert(fun_ptr1 == &plus);
  assert((*fun_ptr1)(5) == 6);
  assert((*fun_ptr1)(5) == plus(5));
  assert(fun_ptr2 != fun_ptr1);
  assert((*fun_ptr2)(5) == 4);
  return 0;
}
