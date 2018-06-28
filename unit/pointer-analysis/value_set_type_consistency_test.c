
#include <stdlib.h>

static char global_object;

struct composite {
  int x;
  int y;
};

int main(int argc, char **argv) {

  char stack_object;
  char *dynamic_pointer = (char*)malloc(1);
  char *stack_pointer = &stack_object;
  char *global_pointer = &global_object;
  // Integer -> pointer is denoted integer_address, but float -> pointer gets a
  // general ID_unknown.
  char *unknown_pointer = (char*)1.0;

  char *any_pointer =
    argc == 0 ? dynamic_pointer :
    argc == 1 ? stack_pointer :
    argc == 2 ? global_pointer :
    unknown_pointer;

  char *dynamic_pointer_with_offset = &(dynamic_pointer[4]);
  char *stack_pointer_with_offset = &(stack_pointer[4]);
  char *global_pointer_with_offset = &(global_pointer[4]);
  char *unknown_pointer_with_offset = &(unknown_pointer[4]);

  struct composite *unknown_struct_pointer = (struct composite *)1.0;
  int *unknown_member_pointer = &(unknown_struct_pointer->y);
}
