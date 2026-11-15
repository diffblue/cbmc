#include <initializer_list>
#include <vector>
extern "C" void __CPROVER_assert(bool, const char *);
static int live = 0;
struct rec {
  int a;
  rec(int x) : a(x) { ++live; }
  rec(const rec &o) : a(o.a) { ++live; }
  ~rec() {
    --live;
    a = -1;
  }
};
int main() {
  {
    std::vector<rec> v{rec{1}, rec{2}, rec{3}};
    __CPROVER_assert(v[0].a + v[1].a + v[2].a == 6,
                     "elements copied while alive");
    __CPROVER_assert(live == 3, "list elements destroyed");
  }
  __CPROVER_assert(live == 0, "each object destroyed once");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
