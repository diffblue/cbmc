#include <assert.h>
#include <stdlib.h>

extern int nondet_int();

int main() {

  int arraylen=nondet_int();

  if(arraylen==3)
  {
    int** array_init = malloc(sizeof(int *)*arraylen);

    // mis-align that pointer!
    char * char_ptr = (char *) array_init;
    char_ptr++;

    int local_var;

    int **array2=(int**)char_ptr;

    // write
    array2[0]=&local_var;

    // check
    int value=*array2[0];

    assert(value==local_var);
  }

}
