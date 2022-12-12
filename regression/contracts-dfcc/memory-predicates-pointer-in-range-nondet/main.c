#include <stdbool.h>
#include <stdlib.h>

// A vtable is a struct containing function pointers
typedef struct vtable_s
{
  int (*f)(void);
} vtable_t;

int return_0()
{
  return 0;
}

int return_1()
{
  return 1;
}

// we have two possible vtables
vtable_t vtable_0 = {.f = &return_0};
vtable_t vtable_1 = {.f = &return_1};

// foo takes a vtable and calls f
int foo(vtable_t *vtable)
  // clang-format off
__CPROVER_requires(
  // vtable is nondeterministic pointer to one of two objects
    __CPROVER_pointer_in_range_dfcc(&vtable_0, vtable, &vtable_0) ||
    __CPROVER_pointer_in_range_dfcc(&vtable_1, vtable, &vtable_1))
__CPROVER_ensures(__CPROVER_return_value == 0 || __CPROVER_return_value == 1)
// clang-format on
{
CALL:
  return vtable->f();
}

int main()
{
  vtable_t *vtable;
  foo(vtable);
}
