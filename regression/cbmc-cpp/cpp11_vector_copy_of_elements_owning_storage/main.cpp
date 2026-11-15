#include <vector>
extern "C" void __CPROVER_assert(bool, const char *);
struct rec {
  std::vector<int> v;
  rec() : v(1, 3) {}
};
int main() {
  std::vector<rec> a(1);
  {
    std::vector<rec> b(a);
    b[0].v[0] = 4;
    __CPROVER_assert(a[0].v[0] == 3, "copy owns its storage");
  }
  __CPROVER_assert(a[0].v[0] == 3, "source intact");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
