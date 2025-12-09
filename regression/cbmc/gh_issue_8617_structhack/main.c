#include <assert.h>
#include <stdlib.h>

// Reproduction case for struct hack bug reported for CBMC 5.12
// Bug: When a struct with a flexible array member is allocated with extra
// space, CBMC incorrectly fails assertions when accessing elements beyond
// the declared size.

struct Foo
{
  int i;
  char data[1];
};

int main()
{
  struct Foo *foo = malloc(sizeof(struct Foo) + sizeof(char) * 2);
  assert(foo);
  foo->data[0] = 'a';
  assert(foo->data[0] == 'a'); // always succeeds
  foo->data[1] = 'b';          // set data[1]
  assert(foo->data[1] == 'b'); // check data[1] -- should succeed
  foo->data[2] = 'c';          // set data[2]
  assert(
    foo->data[1] == 'b'); // check data[1] again - this used to fail in 5.12

  return 0;
}
