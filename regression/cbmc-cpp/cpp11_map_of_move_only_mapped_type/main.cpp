#include <map>
#include <utility>
extern "C" void __CPROVER_assert(bool, const char *);
// goto_functiont's shape: move-only
struct move_only
{
  int v;
  explicit move_only(int x) : v(x)
  {
  }
  move_only(const move_only &) = delete;
  move_only(move_only &&o) : v(o.v)
  {
  }
  move_only &operator=(const move_only &) = delete;
  move_only &operator=(move_only &&o)
  {
    v = o.v;
    return *this;
  }
};
int main()
{
  // pair<const int, move_only>'s defaulted copy constructor is defined as
  // deleted ([class.copy.ctor]/10); it must not be elaborated
  std::map<int, move_only> m;
  m.emplace(1, move_only(5));
  __CPROVER_assert(m.at(1).v == 5, "move-only mapped type");
  __CPROVER_assert(m.at(1).v == 6, "WRONG (must FAIL)");
}
