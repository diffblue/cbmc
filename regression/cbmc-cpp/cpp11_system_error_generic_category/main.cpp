// N5008 [syserr.errcat.objects]/1-2: generic_category() and
// system_category() refer to objects whose name() is "generic" and
// "system"; [syserr.syserr.members]/2: a system_error holds the error_code
// it was constructed with.  libstdc++ defines the category functions in its
// compiled library.
#include <cstring>
#include <system_error>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  int code = 0;
  bool generic = false, same = false, other = false;
  try
  {
    throw std::system_error(std::make_error_code(std::errc::io_error));
  }
  catch(const std::system_error &e)
  {
    code = e.code().value();
    generic = std::strcmp(e.code().category().name(), "generic") == 0;
    same = &e.code().category() == &std::generic_category();
    other = &std::system_category() != &std::generic_category() &&
            std::strcmp(std::system_category().name(), "system") == 0;
  }
  __CPROVER_assert(
    code == int(std::errc::io_error) && generic && same && other,
    "the generic category");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
