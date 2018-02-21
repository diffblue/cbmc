#include <assert.h>
#include <stdlib.h>

struct ComplexStruct
{
  struct
  {
    int some_variable;
    const int some_constant;
  } struct_contents;
  union {
    int some_integer;
    double some_double;
  } union_contents;
  struct ComplexStruct *pointer_contents;
};

void havoc_complex_struct(struct ComplexStruct *p);

int main(void)
{
  struct ComplexStruct child_struct = {{11, 21}, {.some_integer = 31}, NULL};
  struct ComplexStruct main_struct = {
    {10, 20}, {.some_double = 13.0}, &child_struct};
  assert(main_struct.pointer_contents->struct_contents.some_variable == 11);
  assert(main_struct.struct_contents.some_variable == 10);
  assert(main_struct.struct_contents.some_constant == 20);
  assert(
    main_struct.union_contents.some_double < 14.0 &&
    main_struct.union_contents.some_double > 12.0);

  havoc_complex_struct(&main_struct);

  // everything (except constants) in the main struct was havocced
  assert(main_struct.pointer_contents->struct_contents.some_variable == 11);
  assert(main_struct.struct_contents.some_variable == 10);
  assert(main_struct.struct_contents.some_constant == 20);
  assert(
    main_struct.union_contents.some_double < 14.0 &&
    main_struct.union_contents.some_double > 12.0);
  // the child struct was NOT havocced because we can't follow pointers
  assert(child_struct.struct_contents.some_variable == 11);
  assert(child_struct.union_contents.some_integer == 31);
  assert(!child_struct.pointer_contents);
}
