#include <assert.h>
#include <stdlib.h>

struct linked_list
{
  struct linked_list *next;
};

#ifdef _WIN32
#  ifdef _M_X64
#    define POINTER_BYTES 8ul
#  else
#    define POINTER_BYTES 4ul
#  endif
#else
#  define POINTER_BYTES __SIZEOF_POINTER__
#endif

int main(void)
{
  size_t list_sz = POINTER_BYTES;
  assert(list_sz == sizeof(struct linked_list));
  struct linked_list *list = malloc(list_sz);
  // this line makes symex crash for some reason
  // last known to work on 9cf2bfb3e458d419d842a0e1fd26fb1748451851
  // (no bisection has been done yet to narrow down the source of the error)
  list->next = (struct linked_list *)0;
  assert(!list->next);
}
