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

struct struct_containing_fptr
{
  int i;
  fptr_t fptr;
  double d;
};

int main(void)
{
  int nondet_choice;

  // Read from struct
  struct struct_containing_fptr s0, s1;
  s0.fptr = f;
  s1.fptr = g;
  fptr_t fun1;
  if(nondet_choice)
    fun1 = s0.fptr;
  else
    fun1 = s1.fptr;
  fun1(5);

  // Write to struct
  struct struct_containing_fptr s2;
  if(nondet_choice)
    s2.fptr = f;
  else
    s2.fptr = g;
  s2.fptr(5);

  // Array of structs
  struct struct_containing_fptr s_array[3];
  s_array[0] = s0;
  s_array[1] = s1;
  s_array[2] = s2;
  fptr_t fun2 = (s_array + 1)->fptr;
  fun2(5);
}
