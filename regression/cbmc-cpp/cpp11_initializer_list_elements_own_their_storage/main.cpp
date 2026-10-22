// N5008 [dcl.init.list]/5: each element of an initializer list's backing
// array is copy-initialized from the corresponding element of the list, as
// an object of the array.  A class whose pointer member refers to its own
// storage (std::string's local buffer) must refer to the array element's
// storage, not to a temporary's: the temporary is gone when the list is used.
#include <initializer_list>
#include <map>
#include <string>

extern "C" void __CPROVER_assert(bool, const char *);

struct self_ref
{
  char *p;
  char buf[2];
  self_ref(char c) : p(buf)
  {
    buf[0] = c;
    buf[1] = 0;
  }
  self_ref(const self_ref &o) : p(buf)
  {
    buf[0] = o.buf[0];
    buf[1] = 0;
  }
  ~self_ref()
  {
  }
};

struct holder
{
  std::map<std::string, int> m;
  // [dcl.init.list]/3.10, [over.ics.list]/10: the list binds the reference
  // to a temporary initializer_list
  explicit holder(std::initializer_list<std::pair<const std::string, int>> &&il)
    : m{il}
  {
  }
};

int main()
{
  std::initializer_list<self_ref> l{'n', 'l'};
  __CPROVER_assert(l.begin()[1].p == l.begin()[1].buf, "own buffer");
  __CPROVER_assert(l.begin()[1].p[0] == 'l', "through the pointer");

  std::initializer_list<std::string> sl{"n", "l"};
  __CPROVER_assert(
    sl.begin()[0][0] == 'n' && sl.begin()[1][0] == 'l', "string");

  holder h({{"n", 2}, {"l", 3}});
  __CPROVER_assert(h.m.size() == 2, "map from a list bound to a reference");
  __CPROVER_assert(h.m.size() == 1, "WRONG (must FAIL)");
  return 0;
}
