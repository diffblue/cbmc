// std::map's _Rb_tree has members defined out of line; a std::map member of
// a struct declared in an extern "C" block (a C header used from C++)
// instantiated them with C linkage.
#include <map>
extern "C" void __CPROVER_assert(bool, const char *);
extern "C"
{
  typedef enum
  {
    KIND_A,
    KIND_B
  } kind_t;
  typedef struct settings
  {
    std::map<kind_t, unsigned> sizes;
  } settings_t;
}
int main()
{
  settings_t s;
  s.sizes[KIND_B] = 4;
  __CPROVER_assert(s.sizes.size() == 1, "inserted");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
