#include <assert.h>

unsigned int x;
unsigned int y;

unsigned int nondet_int()
{
  unsigned int z;
  return z;
}

void checkpoint()
{
}

unsigned int complex_function_which_returns_one()
{
  unsigned int i = 0;
  while(++i < 1000001)
  {
    if(nondet_int() && ((i & 1) == 1))
      break;
  }
  return i & 1;
}

void fill_array(unsigned int *arr, unsigned int size)
{
  for(unsigned int i = 0; i < size; i++)
    arr[i] = nondet_int();
}

unsigned int array_sum(unsigned int *arr, unsigned int size)
{
  unsigned int sum = 0;
  for(unsigned int i = 0; i < size; i++)
    sum += arr[i];
  return sum;
}

const unsigned int array_size = 100000;

int main()
{
  x = complex_function_which_returns_one();
  unsigned int large_array[array_size];
  fill_array(large_array, array_size);
  y = array_sum(large_array, array_size);
  checkpoint();
  assert(y + 2 > y); //y is nondet -- may overflow
  assert(0);
  return 0;
}
