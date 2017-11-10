#include <string.h>

void my_f(void *) { }
void my_h(void *) { }

void my_function()
{
  void *o1;
  my_f(o1); // T1 source

  void *o2;
  memcpy(o2, o1, 100);

  my_h(o2); // T1 sink
}
