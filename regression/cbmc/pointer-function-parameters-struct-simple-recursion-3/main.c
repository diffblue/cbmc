#include <assert.h>
#include <stdlib.h>

typedef struct st
{
  struct st *next;
  int data;
} st_t;

st_t dummy;

void func(st_t *p)
{
  if(p != NULL)
  {
    if(p->next != NULL)
    {
      if(p->next->next != NULL)
      {
        // covered
      }
      else
      {
        // covered
      }
    }
    else
    {
      // not covered
    }
  }
  else
  {
    // not covered
  }
}
