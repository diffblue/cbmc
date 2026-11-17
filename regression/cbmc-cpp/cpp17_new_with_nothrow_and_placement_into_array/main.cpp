#include <new>
extern "C" void __CPROVER_assert(bool, const char *);
struct P {
  int x;
};
int main() {
  P *a = new (std::nothrow) P[3];
  if (a != nullptr) {
    a[2].x = 1;
    __CPROVER_assert(a[2].x == 1, "nothrow new[]");
    delete[] a;
  }
  P *b = new (std::nothrow) P;
  __CPROVER_assert(b != (P *)&std::nothrow, "nothrow new");
  delete b;
  P *c = new (std::align_val_t{64}, std::nothrow) P[2];
  if (c != nullptr) {
    c[1].x = 2;
    __CPROVER_assert(c[1].x == 2, "aligned nothrow new[]");
    delete[] c;
  }
  alignas(P) unsigned char buffer[2 * sizeof(P)];
  P *d = new (buffer) P;
  __CPROVER_assert((void *)d == (void *)buffer, "placement new into an array");
  P *e = new (buffer) P[2];
  e[1].x = 3;
  __CPROVER_assert(((P *)buffer)[1].x == 3, "placement new[] into an array");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
