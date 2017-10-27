#include <stdlib.h>

void my_f(void *) { }
void my_h(void *) { }

void my_function()
{
  struct some_struct
  {
    void *data;
  } whatnot;

  my_f(whatnot.data); // T1 source
  my_h(whatnot.data); // T1 sink

  // via a copy
  void *o=whatnot.data;
  my_h(o); // T1 sink

  // copy entire struct
  struct some_struct whatelse;
  whatelse=whatnot;
  my_h(whatelse.data); // T1 sink
}
