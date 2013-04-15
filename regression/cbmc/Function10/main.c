#include <assert.h>

int global;

void other_func1(int z, int my_func(int b, int c))
{
  my_func(1, 2);
}

void other_func2(int z, int my_func(int b, int c), int y)
{
}

void my_f1(int array[*]);

void my_f1(int array[])
{
}

int whatnot(int p1, int p2)
{
  global=p2;
}

int main()
{
  int *p;
  my_f1(p);
  
  other_func1(1, whatnot);
  assert(global==2);
}
