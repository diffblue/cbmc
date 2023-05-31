#include <assert.h>
#include <stdint.h>

struct my_struct_type
{
  int16_t a;
  int16_t b;
};

int main()
{
  int16_t nondet;
  struct my_struct_type my_struct;
  if(nondet == 3)
    my_struct.a = 10;
  else
    my_struct.a = 12;
  struct my_struct_type struct_copy;
  struct_copy = my_struct;
  assert(my_struct.b != 30 || struct_copy.a != 10);
}
