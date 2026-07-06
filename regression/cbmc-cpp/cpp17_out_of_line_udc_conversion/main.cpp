// KNOWNBUG (faithful reproducer of the tempfile.cpp dog-food failure).
//
// N5008 [over.match.best] + [over.ics.user] + [temp.deduct]: overload
// resolution of `std::filesystem::remove(name)` (name : std::string) selects
// `remove(const path&)` by forming the user-defined conversion
// std::string -> std::filesystem::path through path's (templated,
// SFINAE-guarded) converting constructor.  The viability of that conversion
// depends only on the source and destination types -- NOT on the scope of the
// call site.
//
// CBMC wrongly rejects this call ("found no match for symbol 'remove'" ->
// CONVERSION ERROR) whenever it appears inside an OUT-OF-LINE, qualified
// function definition (a class member such as `wrapper::cleanup` below, but
// also a namespace member `N::f` or a static member), while the identical call
// in a free function at namespace scope resolves correctly.  The distinguishing
// factor is purely that the current scope during overload resolution is a
// nested (out-of-line-definition) scope: the string->path converting-
// constructor template fails to resolve there.
//
// Reduced from src/util/tempfile.cpp (`temporary_filet::~temporary_filet`)
// using cvise while keeping the real <string>/<filesystem> includes, so the
// libstdc++ side stays faithful.  Flip to CORE once the conversion resolves
// independently of the call-site scope.

#include <string>

extern "C" void __CPROVER_assert(int, const char *);

// The class is fully defined before <filesystem> is included; its member
// function is then defined out-of-line, after <filesystem>.
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
  wrapper w;
  w.name = "does-not-exist";
  __CPROVER_assert(w.cleanup() == 42, "out-of-line member compiles and runs");
  __CPROVER_assert(w.cleanup() == 7, "WRONG: must fail");
  return 0;
}
