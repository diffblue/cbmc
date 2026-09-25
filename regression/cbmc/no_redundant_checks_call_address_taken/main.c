#include <stdlib.h>

// A callee that writes through a pointer-to-pointer argument, changing the
// caller's local pointer.
void clobber(int **pp)
{
  *pp = NULL;
}

int main()
{
  int x = 0;
  int *p = &x;

  int y = *p; // valid here -- this caches a "p is a valid pointer" assertion

  clobber(&p); // p's address is passed in; the callee sets p to NULL

  int z = *p; // p is now NULL: this dereference must still be checked

  return y + z;
}
