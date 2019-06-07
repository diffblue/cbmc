#include <assert.h>

int plus(int i)
{
  return i + 1;
}

int minus(int i)
{
  return i - 1;
}

typedef int (*fun_ptrt)(int);
fun_ptrt fun_array[2];

fun_ptrt fun_ptr1;
fun_ptrt fun_ptr2;

void initialize()
{
  fun_array[0] = &plus;
  fun_array[1] = &minus;
  fun_ptr1 = *fun_array;
  fun_ptr2 = fun_array[1];
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
