#include <assert.h>

struct S
{
  unsigned char : 0;
  unsigned char : 0;
  unsigned char value;
};

union U
{
  struct S structure;
  unsigned char value;
};

int main(int argc, char **argv)
{
  (void)argv;
  unsigned char value = (unsigned char)argc;

  union U object = {.structure = {.value = value}};
  assert(object.value == value);
}
