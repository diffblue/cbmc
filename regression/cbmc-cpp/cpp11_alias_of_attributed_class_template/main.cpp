extern "C" void __CPROVER_assert(bool, const char *);
typedef unsigned short uint16_t;
typedef unsigned char uint8_t;
template <typename T>
struct G
{
  T a;
  uint8_t b;
} __attribute__((packed, aligned(16)));
using lreg_t = G<uint16_t> __attribute__((aligned(16)));
int main()
{
  lreg_t r;
  r.a = 1;
  __CPROVER_assert(sizeof(lreg_t) == 16, "alias of attributed template");
  __CPROVER_assert(r.a == 1, "usable");
  return 0;
}
