// N5008 [pairs.pair]: pair's converting constructor
// pair(U1&&, U2&&) initializes first/second from the forwarded
// arguments.  In C++20 libstdc++ (GCC 13) this constructor is
// constrained with a requires-clause and explicit(bool):
//   constexpr explicit(...) pair(_U1&& __x, _U2&& __y)
//
// KNOWNBUG: the front end creates the instantiated constructor symbol
// flagged constexpr/macro but NEVER converts its body (nil value, not
// in the deferred queue), and symex treats the bodyless call as havoc:
// both members are nondeterministic garbage.  --cpp17 (whose pair uses
// enable_if instead of requires/explicit(bool)) works.
//
// This is the REAL remaining blocker for cpp20_map_basic:
// _Rb_tree::_M_get_insert_unique_pos returns _Res(__y, 0), whose
// literal 0 selects exactly this converting constructor; the insert
// position pair is garbage, so insert misbehaves.
//
// g++/clang++ verify at runtime.  Flip to CORE when fixed.
extern "C" void __CPROVER_assert(bool, const char *);
#include <utility>

struct nodet
{
  int v;
};

int main()
{
  nodet n{1};
  nodet *y = &n;
  std::pair<nodet *, nodet *> b(y, 0);
  __CPROVER_assert(b.first == &n, "first is y");
  __CPROVER_assert(b.second == nullptr, "second is null");
  return 0;
}
