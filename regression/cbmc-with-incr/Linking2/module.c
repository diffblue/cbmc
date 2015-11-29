#include <assert.h>

#include "module.h"

// the typedefs are local!
typedef int t;

// transitively, this one is different!
struct my_struct
{
  t t_field;
};  

// this one is local, tool!
static t i=1;

// shared
int j;

void f()
{
  assert(i==1);
  assert(j==3);
  i=3;
  j=4;
  
  struct my_struct xx;
  assert(sizeof(xx.t_field)==sizeof(int));
}

// same for structs

struct struct_tag
{
  int i;
};
