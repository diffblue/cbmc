#include <assert.h>
#include <stdlib.h>

extern int nondet_int();

int main() {

  int arraylen=nondet_int();

  if(arraylen==3)
  {
    int** array_init = malloc(sizeof(int *)*arraylen);

    int a0, a1, a2;

    array_init[0] = &a0;
    array_init[1] = &a1;
    array_init[2] = &a2;

    void **local_array=(void**)array_init;

    int *address=(int *)local_array[0];
    assert(address==&a0);
  }

}
