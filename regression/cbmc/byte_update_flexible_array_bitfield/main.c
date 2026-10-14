// Regression test for an invariant violation in bv_to_array_expr
// (src/util/lower_byte_operators.cpp): "subtype width times array size
// should be total bitvector width".
//
// A struct that has a bit-field followed by a flexible array member is
// reconstructed from a flat bit-vector when a byte-wise operation such
// as memset is lowered.  The flexible array member is typechecked to a
// zero-length array (int[0]).  bv_to_struct_expr handled the zero-width
// component by passing the *entire* bit-vector to bv_to_array_expr,
// which then saw num_elements==0 but a non-zero total width and tripped
// the data invariant.
//
// The bit-field is required: it forces the struct to be lowered through
// the byte operators.  A struct with a plain scalar field followed by a
// flexible array member does not reach this path.

#include <string.h>

struct s
{
  int flag : 5;
  int data[];
};

int main(void)
{
  struct s obj;
  memset(&obj, 0, sizeof(obj));
  return 0;
}
