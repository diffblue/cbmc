#include <assert.h>

typedef struct list
{
  int datum;
  struct list *next;
} list_nodet;

list_nodet *global_list;
void test_function(void)
{
  int i = 0;
  list_nodet *list_walker = global_list;
  while(list_walker)
  {
    list_walker->datum = ++i;
    list_walker = list_walker->next;
  }
  list_walker = global_list;
  i = 0;
  while(list_walker)
  {
    assert(list_walker->datum == ++i);
    list_walker = list_walker->next;
  }
}
