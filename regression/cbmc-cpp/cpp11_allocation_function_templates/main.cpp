#include <cstddef>
extern "C" void __CPROVER_assert(bool, const char *);
static unsigned char arena[64];
struct pool {};
template <class A> void *operator new(std::size_t, A &) { return arena; }
template <class T> T *make(pool &p) { return new (p) T(4); }
template <class T> struct box {
  T v;
  void *operator new(std::size_t) { return arena + 32; }
};
int main() {
  pool p;
  int *i = make<int>(p);
  __CPROVER_assert((void *)i == arena && *i == 4,
                   "allocation function template");
  box<int> *b = new box<int>{5};
  __CPROVER_assert((void *)b == arena + 32 && b->v == 5,
                   "member of a class template");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
