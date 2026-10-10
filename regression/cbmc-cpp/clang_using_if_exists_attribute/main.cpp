// Clang's __attribute__((using_if_exists)) on a using-declaration (a clang
// extension, used throughout libc++'s <cstdlib>, <cstdio>, ... for C library
// names a platform may lack): if the name does not exist, the declaration is
// ignored, and only a use of the name is an error.  CBMC rejects the
// declaration itself ("using identifier 'no_such_thing' not found").
extern "C" void __CPROVER_assert(bool, const char *);

int exists;

namespace ns
{
using ::no_such_thing __attribute__((__using_if_exists__));
using ::exists __attribute__((__using_if_exists__));
} // namespace ns

int main()
{
  ns::exists = 1;
  __CPROVER_assert(exists == 1, "existing name");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
