#include <cstddef>
#include <new>
extern "C" void __CPROVER_assert(bool, const char *);
alignas(64) static unsigned char arena[256];
static std::size_t used = 0;
static int allocations = 0, deallocations = 0, destroyed = 0;
static std::size_t last_size = 0;
static void *last_freed = nullptr;

struct pool {};
void *operator new(std::size_t n, pool &) {
  ++allocations;
  void *p = arena + used;
  used += (n + 15) / 16 * 16;
  return p;
}

struct node {
  int v;
  node(int x) : v(x) {}
  void *operator new(std::size_t n) {
    ++allocations;
    last_size = n;
    void *p = arena + used;
    used += (n + 15) / 16 * 16;
    return p;
  }
  void operator delete(void *p) {
    ++deallocations;
    last_freed = p;
  }
};
struct derived : node {
  int w = 2;
  derived() : node(1) {}
};

struct counted {
  int v = 4;
  ~counted() { ++destroyed; }
  void *operator new[](std::size_t n) {
    last_size = n;
    void *p = arena + used;
    used += (n + 15) / 16 * 16;
    return p;
  }
  void operator delete[](void *p) {
    ++deallocations;
    last_freed = p;
  }
};

struct maybe {
  int v = 5;
  void *operator new(std::size_t, int fail) noexcept {
    return fail ? nullptr : arena + 240;
  }
  void operator delete(void *) {}
};

int main() {
  pool pl;
  int *i = new (pl) int(7);
  __CPROVER_assert((void *)i == arena && *i == 7 && allocations == 1,
                   "global placement");

  node *n = new node(3);
  __CPROVER_assert((void *)n == arena + 16 && n->v == 3 &&
                       last_size == sizeof(node),
                   "class allocation function");
  delete n;
  __CPROVER_assert(deallocations == 1 && last_freed == arena + 16,
                   "class deallocation function");

  derived *d = new derived;
  __CPROVER_assert(last_size == sizeof(derived) && d->w == 2,
                   "inherited allocation");

  node *g = ::new node(9);
  __CPROVER_assert(allocations == 3 && g->v == 9, "::new uses the global");
  ::delete g;
  __CPROVER_assert(deallocations == 1, "::delete uses the global");

  counted *c = new counted[3];
  __CPROVER_assert(c[2].v == 4 && last_size > 3 * sizeof(counted),
                   "array with cookie");
  delete[] c;
  __CPROVER_assert(destroyed == 3 && deallocations == 2, "array deleted");

  maybe *m = new (1) maybe;
  __CPROVER_assert(m == nullptr, "non-throwing allocation failed");
  maybe *m2 = new (0) maybe;
  __CPROVER_assert(m2 != nullptr && m2->v == 5, "non-throwing allocation");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
