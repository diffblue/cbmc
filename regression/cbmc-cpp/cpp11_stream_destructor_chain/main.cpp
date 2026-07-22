// Destroying any iostream object runs the chain ~basic_stringstream ->
// ~basic_iostream -> ... -> ~basic_ios -> ~ios_base.  The virtual-base
// destructors receive a pointer converted to the base class; writing
// the vtable pointers during destruction
// (this->ios_base@vtable_pointer, this->basic_ios@vtable_pointer)
// fails the pointer bounds checks.  FIXED 2026-07-22 (see test.desc).
// Original diagnosis kept below for the record.
// DIAGNOSIS 2026-07-21 (late): the
// failing ~basic_ios frames are reached via DEVIRTUALIZED dispatch
// from unrelated destructor sites (__pthread_cleanup_class's void*
// __cancel_arg; std::locale facet cache teardown), where the object's
// vtable pointer is unconstrained (facet constructors unmodeled), so
// remove_virtual_functions' candidate set lets ~basic_ios run on an
// object smaller than basic_ios (member offset 200+8 > object size).
// A dispatch-precision/vtable-constraint issue, not a layout bug: a
// header-free diamond with virtual destructors verifies clean.
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
