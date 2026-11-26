// N5008 [basic.def.odr]/15: an inline function defined in a header that a
// C++ and a C translation unit both include has one definition.  The two
// front ends name the members of the header's struct differently
// (`stream::position', `position'), so the linker saw two different types;
// the Windows SDK's stdio.h has such inline functions, and linking CBMC's C
// library models (preprocessed by cl) failed.
#include "shared.h"

extern "C" void __CPROVER_assert(bool, const char *);

int main()
{
  stream s = {3};
  __CPROVER_assert(stream_position(&s) == 3, "C++ caller");
  __CPROVER_assert(c_side(&s) == 4, "C caller");
  __CPROVER_assert(c_side(&s) == 5, "WRONG (must FAIL)");
  return 0;
}
