// N5008 [namespace.unnamed]/1: an unnamed namespace behaves as
//   namespace UNIQUE {} using namespace UNIQUE; namespace UNIQUE { body }
// so its members are visible in the enclosing scope, and all unnamed
// blocks in the same scope share ONE unique namespace.  CBMC's converter
// returned before converting the body items, so every entity declared in
// an unnamed namespace was silently dropped ("symbol ... is unknown" at
// use).  Found dog-fooding src/goto-programs/validate_goto_model.cpp.
// g++/clang++ accept and verify at runtime.
extern "C" void __CPROVER_assert(bool, const char *);

namespace
{
class validatort
{
public:
  int x;
  explicit validatort(int v) : x(v)
  {
  }
};
} // namespace

namespace
{
// second unnamed block: same unique namespace, sees earlier members
int probe(const validatort &v)
{
  return v.x + 1;
}
} // namespace

int main()
{
  validatort v{7};
  __CPROVER_assert(v.x == 7, "unnamed-namespace class usable");
  __CPROVER_assert(probe(v) == 8, "second block shares the namespace");
  return 0;
}
