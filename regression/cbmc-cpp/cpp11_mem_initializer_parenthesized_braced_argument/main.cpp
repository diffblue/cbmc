// N5008 [class.base.init]/7, [dcl.init.general]/16.6.2: the mem-initializer
// `h({true})' direct-initializes h from an expression-list with one
// argument, the braced-init-list, which initializes the `seq &&' parameter
// through seq's initializer-list constructor.  The front end unwrapped the
// list as for a braced mem-initializer `h{true}' and looked for a
// constructor of holder taking a bool: "found no match for symbol 'holder'"
// (std::stack<bool>'s `record_events({true})', CBMC's own
// goto_symex_statet, dog-fooding).
extern "C" void __CPROVER_assert(bool, const char *);
#include <initializer_list>
struct seq
{
  int n = 0;
  seq(std::initializer_list<bool> l) : n(int(l.size()) + 10)
  {
  }
};
struct holder
{
  int got;
  explicit holder(seq &&s) : got(s.n)
  {
  }
};
struct state
{
  holder h;
  // N5008 [class.base.init]/7, [dcl.init.general]/16.6.2: the
  // expression-list `({true})' direct-initializes h with one argument, the
  // braced-init-list, which initializes the seq parameter
  state() : h({true})
  {
  }
};
int main()
{
  state s;
  __CPROVER_assert(s.h.got == 11, "mem-initializer with a braced argument");
  holder local({true, false});
  __CPROVER_assert(local.got == 12, "local");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
