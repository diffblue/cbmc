// Destroying any iostream object runs the chain ~basic_stringstream ->
// ~basic_iostream -> ... -> ~basic_ios -> ~ios_base.  The virtual-base
// destructors receive a pointer converted to the base class; writing
// the vtable pointers during destruction
// (this->ios_base@vtable_pointer, this->basic_ios@vtable_pointer)
// fails the pointer bounds checks: CBMC's flattened single-copy layout
// of the virtual bases does not line up with member offsets computed
// against the base class's own layout.  A header-free diamond with
// virtual destructors verifies clean, so the trigger involves the
// full iostream shape (out-of-line destructors + vtables).
// ios_base's library-defined constructor/destructor themselves are
// modeled (empty bodies, [ios.base.cons]/1) since 2026-07-21.
// The remaining blocker for cpp11_stream_setw /
// cpp11_ofstream_from_string.
// g++/clang++ accept and verify at runtime.
#include <sstream>
extern "C" void __CPROVER_assert(bool, const char *);

int main()
{
  {
    std::stringstream ss;
  } // full destructor chain runs here
  int reached = 1;
  __CPROVER_assert(reached == 1, "stream destructor chain verifies");
  return 0;
}
