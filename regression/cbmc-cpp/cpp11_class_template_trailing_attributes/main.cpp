extern "C" void __CPROVER_assert(bool, const char *);
typedef unsigned short uint16_t;
typedef unsigned char uint8_t;
template <typename T>
struct G
{
  T a;
  uint8_t b;
} __attribute__((packed, aligned(16)));
int main()
{
  G<uint16_t> g;
  g.a = 7;
  g.b = 3;
  static_assert(sizeof(G<uint16_t>) == 16, "packed then aligned(16)");
  static_assert(sizeof(G<uint8_t>) == 16, "second instantiation");
  __CPROVER_assert(
    g.a == 7 && g.b == 3, "attributed class template instantiates");
  return 0;
}
