#include <assert.h>

int my_func(int stat_loc)
{
  #ifdef __GNUC__
  // This is a 'temporary union', yet another gcc extension.
  // Visual Studio won't do it.
  return ((union { __typeof__(stat_loc) __in; int __i; })
    { .__in =(stat_loc) }).__i;
  #endif
}

int main(void)
{
  #ifdef __GNUC__
  int x;
  assert(my_func(x)==x);

  union my_U
  {
    int z;
    char ch;
    float f;
  } union_object;

  float some_float=1.5f;

  // This is the 'union constructor', which is
  // yet another gcc extension.
  // Visual Studio won't do it.
  union_object=(union my_U)some_float;

  assert(union_object.f==1.5f);
  #endif
}
