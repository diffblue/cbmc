#include <vector>
extern "C" void __CPROVER_assert(bool, const char *);
struct rec {
  int a;
  std::vector<int> v;
  explicit rec(int x) : a(x), v(1, x) {}
};
struct holder {
  int sum(const std::vector<rec> &l) {
    int s = 0;
    for (const rec &r : l)
      s += r.a + r.v[0];
    return s;
  }
  int wrap(const rec *output) { return sum(std::vector<rec>{*output}); }
  int wrap2(const rec &first, const rec &second) {
    return sum(std::vector<rec>{first, second, rec{5}});
  }
};
int main() {
  holder h;
  rec r{3};
  rec q{4};
  __CPROVER_assert(h.wrap(&r) == 6, "element copied from a parameter");
  __CPROVER_assert(h.wrap(&q) == 8, "evaluated per call");
  __CPROVER_assert(h.wrap2(r, q) == 6 + 8 + 10, "mixed elements");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
