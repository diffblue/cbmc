#include <assert.h>

#include "module.h"

// t is different in the other file
typedef char t;

// transitively, this one is different!
struct my_struct
{
  t t_field;
};

// the other one is static, and thus, this one is local
t i=2;

// this is shared
int j=3;

int main()
{
  assert(i==2);
  assert(j==3);
  
  f(); // does not change i,
       // but does change j
  
  assert(i==2);
  assert(j==4);
  
  struct my_struct xx;
  assert(sizeof(xx.t_field)==1);
}

struct struct_tag
{
  short int i;
};
