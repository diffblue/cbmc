// N5008 [pairs.pair]: pair's converting constructor
// pair(U1&&, U2&&) initializes first/second from the forwarded
// arguments.  In C++20 libstdc++ (GCC 13) this constructor is
// constrained with a requires-clause and explicit(bool):
//   constexpr explicit(...) pair(_U1&& __x, _U2&& __y)
// The requires-clause calls the static consteval member
// _S_constructible<...>() (cpp20_requires_static_call_atom,
// cpp20_requires_class_param_atom).  std::map's
// _Rb_tree::_M_get_insert_unique_pos returns _Res(__y, 0), whose literal 0
// selects this constructor (cpp20_map_basic).  g++/clang++ verify at
// runtime.
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
