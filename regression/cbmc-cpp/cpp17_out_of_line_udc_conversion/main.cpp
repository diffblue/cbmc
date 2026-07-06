// N5008 [over.match.best] + [over.ics.user] + [temp.deduct] +
// [class.ctor.general]: overload resolution of `std::filesystem::remove(name)`
// (name : std::string) selects `remove(const path&)` by forming the
// user-defined conversion std::string -> std::filesystem::path through path's
// converting constructor.  A conversion's viability depends only on the source
// and destination types, not on the scope of the call site.
//
// This call is written inside an OUT-OF-LINE, qualified member definition
// (`wrapper::cleanup`, defined after <filesystem> is included).  CBMC used to
// reject it ("found no match for symbol 'remove'" -> CONVERSION ERROR) because,
// while type-checking the (deferred) out-of-line body, std::filesystem::path's
// constructor components were not yet materialised, so the converting-
// constructor conversion could not be formed -- even though the identical call
// in a free function at namespace scope resolved fine.  Fixed in cpp_constructor
// by resolving a class's constructor by the class's own name when no
// constructor component is present (a constructor is named after its class),
// letting overload resolution in the class scope find it.
//
// Reduced from src/util/tempfile.cpp (`temporary_filet::~temporary_filet`)
// using cvise while keeping the real <string>/<filesystem> includes.
//
// The property under test is a *front-end* one -- that the out-of-line body is
// accepted -- so `cleanup()` is intentionally not called from main (its heavy
// std::filesystem/locale machinery need not be symbolically executed); the mere
// fact that the translation unit type-checks exercises the fix.

#include <string>

extern "C" void __CPROVER_assert(int, const char *);

struct wrapper
{
  std::string name;
  int cleanup();
};

#include <filesystem>

int wrapper::cleanup()
{
  std::filesystem::remove(name);
  return 42;
}

int main()
{
  // Reached only if the out-of-line wrapper::cleanup() above type-checked
  // (before the fix the whole translation unit failed with CONVERSION ERROR).
  __CPROVER_assert(sizeof(wrapper) > 0, "front-end accepted the out-of-line body");
  // Non-vacuity guard: a deliberately wrong property that must FAIL.
  __CPROVER_assert(sizeof(wrapper) == 0, "WRONG: must fail");
  return 0;
}
