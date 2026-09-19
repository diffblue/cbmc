#define CONCAT(a, b) a##b
#define CONCAT2(a, b) CONCAT(a, b)

#define STATIC_ASSERT(condition)                                               \
  int CONCAT2(some_array, __LINE__)[(condition) ? 1 : -1]

// `#pragma pack(n)' caps a member's alignment even when the member carries
// an EXACT alignment (`packed, aligned(k)'), and does so for an array
// member as for a scalar one: GCC and clang place both at 2 here.
#pragma pack(push, 2)
struct A
{
  char c;
  signed char m[8] __attribute__((packed, aligned(4)));
};
struct B
{
  char c;
  signed char m __attribute__((packed, aligned(4)));
};
struct E
{
  char c;
  int m __attribute__((packed, aligned(4)));
};
#pragma pack(pop)

STATIC_ASSERT(sizeof(struct A) == 10);
STATIC_ASSERT(__builtin_offsetof(struct A, m) == 2);
STATIC_ASSERT(sizeof(struct B) == 4);
STATIC_ASSERT(__builtin_offsetof(struct B, m) == 2);
STATIC_ASSERT(sizeof(struct E) == 6);
STATIC_ASSERT(__builtin_offsetof(struct E, m) == 2);

int main()
{
  return 0;
}
