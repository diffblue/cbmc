#include <assert.h>

int my_f(int arg)
{
  return arg;
}

int x, y, z;

int main()
{
  #ifdef _WIN32
  
  // Visual Studio won't even parse most of these
  
  #else

  // a side effect inside an array type
  x=1;
  int array[++x];
  assert(x==2);
  assert(sizeof(array)==sizeof(int)*2);

  // same with typedef
  x=1;
  typedef int array_type[++x];
  assert(x==2);
  assert(sizeof(array_type)==sizeof(int)*2);

  // a side effect inside an initializer
  x=1;
  int local=++x, local2=x;
  assert(x==2);
  assert(local==2);
  assert(local2==2);

  // a side effect inside a function argument list
  x=1;
  int return_value=my_f(++x);
  assert(x==2);
  assert(return_value==2);
  
  // using a pointer
  x=1;
  int *p=&x;
  y=++(*p);
  assert(y==2);
  assert(x==2);
  
  // in a struct
  x=1;
  struct struct_type
  {
    int a[++x];
    int b;
  };
  assert(x==2);
  assert(sizeof(struct struct_type)==sizeof(int)*2+sizeof(int));

  // this is evaluated when the type is defined, not later
  x++;
  assert(sizeof(struct struct_type)==sizeof(int)*2+sizeof(int));
  
  // only happens once
  x=1;
  y=1;
  struct other_struct
  {
    int a[++x];
  } v1[y++], v2[y++], v3[y++];
  assert(x==2);
  assert(y==4);
  assert(sizeof(v1)==sizeof(int)*2*1);
  assert(sizeof(v2)==sizeof(int)*2*2);
  assert(sizeof(v3)==sizeof(int)*2*3);
  
  // inside a typecast (struct)
  x=1;
  (struct { int a[x++]; } *)0;
  assert(x==2);
  
  // inside a typecast (function pointer)
  x=1;
  (int (*)(int a[x++]))0; // This is ignored by gcc! Haha!
  assert(x==1);
  
  // inside sizeof
  x=1;
  assert(sizeof(struct { int a[x++]; })==sizeof(int));
  assert(x==2);
  
  // multi-dimensional
  x=y=1;
  typedef int my_array1[x][y];
  x++;
  assert(sizeof(my_array1)==sizeof(int));
  
  #endif
}
