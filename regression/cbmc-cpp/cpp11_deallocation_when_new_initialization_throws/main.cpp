#include <cstddef>
extern "C" void __CPROVER_assert(bool, const char *);
alignas(16) static unsigned char arena[256];
static void *freed = nullptr;
static int placement_freed = 0;
static int tag_seen = 0;

struct pool {
  int tag;
};
void *operator new(std::size_t, pool &) { return arena + 64; }
void operator delete(void *p, pool &pl) {
  ++placement_freed;
  tag_seen = pl.tag;
}

struct thrower {
  int v;
  explicit thrower(int x) : v(x) {
    if (x < 0)
      throw 1;
  }
  void *operator new(std::size_t) { return arena; }
  void operator delete(void *p) { freed = p; }
};

int main() {
  try {
    thrower *t = new thrower(-1);
    (void)t;
  } catch (int) {
  }
  __CPROVER_assert(freed == arena, "deallocated after throwing constructor");

  freed = nullptr;
  thrower *ok = new thrower(1);
  __CPROVER_assert(freed == nullptr && ok->v == 1, "not deallocated");

  pool pl{7};
  try {
    thrower *t = ::new (pl) thrower(-2);
    (void)t;
  } catch (int) {
  }
  __CPROVER_assert(placement_freed == 1 && tag_seen == 7,
                   "placement deallocation");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
