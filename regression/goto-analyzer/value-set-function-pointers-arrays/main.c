#include <assert.h>

typedef int (*fptr_t)(int);

int f(int x)
{
  return x + 1;
}
int g(int x)
{
  return x;
}
int h(int x)
{
  return x - 1;
}

int main(void)
{
  int nondet_choice;

  // Reading from array
  fptr_t fun1;
  fptr_t fun_array1[] = {f, g};
  if(nondet_choice)
    fun1 = fun_array1[0];
  else
    fun1 = fun_array1[1];
  fun1(5);

  // Writing to array
  fptr_t fun_array2[2];
  if(nondet_choice)
    fun_array2[0] = f;
  else
    fun_array2[0] = g;
  fptr_t fun_array3[2];
  fun_array3[0] = fun_array2[0];
  fun_array3[1] = fun_array2[1];
  fun_array3[0](5);
}
