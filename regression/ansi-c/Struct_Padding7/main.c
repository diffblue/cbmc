#define CONCAT(a, b) a##b
#define CONCAT2(a, b) CONCAT(a, b)

#define STATIC_ASSERT(condition)                                               \
  int CONCAT2(some_array, __LINE__)[(condition) ? 1 : -1]

typedef struct S1
{
  int x;
} S1;

#ifdef __GNUC__
struct S2
{
  struct S1 __attribute__((__aligned__(((1L) << 12)))) s1;
};

struct foo
{
  char a;
  int x[2] __attribute__((packed));
};
#endif

int main()
{
#ifdef __GNUC__
  STATIC_ASSERT(sizeof(struct S1) == sizeof(int));
  STATIC_ASSERT(sizeof(struct S2) == (1L << 12));
  STATIC_ASSERT(sizeof(struct foo) == sizeof(char) + 2 * sizeof(int));
#endif
  return 0;
}
