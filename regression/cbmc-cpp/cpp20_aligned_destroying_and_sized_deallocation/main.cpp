#include <cstddef>
#include <new>
extern "C" void __CPROVER_assert(bool, const char *);
alignas(128) static unsigned char arena[512];
static std::size_t got_alignment = 0, got_size = 0;
static int destroyed = 0;
static void *freed = nullptr;

struct alignas(64) wide {
  int v = 1;
  void *operator new(std::size_t n, std::align_val_t a) {
    got_alignment = static_cast<std::size_t>(a);
    return arena + 128;
  }
  void operator delete(void *p, std::align_val_t) { freed = p; }
};

struct self_destroying {
  int v = 3;
  ~self_destroying() { ++destroyed; }
  void *operator new(std::size_t) { return arena + 320; }
  void operator delete(self_destroying *p, std::destroying_delete_t) {
    freed = p;
  }
};

struct sized {
  int v[3];
  void *operator new(std::size_t) { return arena + 384; }
  void operator delete(void *p, std::size_t n) {
    freed = p;
    got_size = n;
  }
};

int main() {
  wide *w = new wide;
  __CPROVER_assert((void *)w == arena + 128 && got_alignment == 64 && w->v == 1,
                   "alignment argument");
  delete w;
  __CPROVER_assert(freed == arena + 128, "aligned deallocation");

  self_destroying *d = new self_destroying;
  delete d;
  __CPROVER_assert(destroyed == 0 && freed == arena + 320,
                   "destroying operator delete");

  sized *s = new sized;
  delete s;
  __CPROVER_assert(freed == arena + 384 && got_size == sizeof(sized),
                   "sized deallocation");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
