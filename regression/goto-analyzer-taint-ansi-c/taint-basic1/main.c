#include <stdlib.h>

void my_f(void *) { }
void my_h(void *) { }
void *my_g(void) { return malloc(1); }

void my_function()
{
  void *o;

  my_f(o); // T1 source
  my_h(o); // T1,T2 sink

  o=my_g(); // T2 source
  my_h(o); // T1,T2 sink
}
