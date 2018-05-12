#include <assert.h>
#include <stdlib.h>

void dynamicAllocationUninitialized(int trigger)
{
  int *obj;
  if(trigger)
  {
    obj = (int *)malloc(sizeof(int));
    *obj = 42;
  }
  else
  {
    obj = (int *)malloc(sizeof(int));
    *obj = 76;
  }

  assert(*obj == 42);
}

int global;
void globalUninitialized(int trigger)
{
  if(trigger)
  {
    global = 44;
  }
  else
  {
    global = 20;
  }

  assert(global == 44);
}

void staticLocalUninitialized(int trigger)
{
  static int staticLocal;
  if(trigger)
  {
    staticLocal = 43;
  }

  assert(staticLocal == 43);
}

void localUninitialized(int trigger)
{
  int local;
  if(trigger)
  {
    local = 24;
  }

  assert(local == 24);
}
