#include <assert.h>

typedef struct list
{
  int datum;
  struct list *next;
} list_nodet;

void test_function(list_nodet *node)
{
  int i = 0;
  list_nodet *list_walker = node;
  while(list_walker)
  {
    list_walker->datum = ++i;
    list_walker = list_walker->next;
  }
  list_walker = node;
  i = 0;
  while(list_walker)
  {
    assert(list_walker->datum == ++i);
    list_walker = list_walker->next;
  }
}
