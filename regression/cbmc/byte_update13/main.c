#include <assert.h>
#include <string.h>

struct blob
{
  unsigned dummy;
  unsigned bit : 1;
};

int main()
{
  struct blob b;
  struct blob b1 = b;

  // Perform byte-wise updates of the struct, up to its full size. Constant
  // propagation made impossible, and thus the byte updates need to be handled
  // by the back-end.
  if(b.dummy <= sizeof(struct blob))
    memset(&b, 0, b.dummy);

  // If we updated the complete struct, then the single-bit bit-field needs to
  // have been set to zero as well. This makes sure that the encoding of byte
  // update properly handles fields that are smaller than bytes.
  assert(b1.dummy != sizeof(struct blob) || b.bit == 0);
}
