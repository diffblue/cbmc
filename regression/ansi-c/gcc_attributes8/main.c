#define CONCAT(a, b) a##b
#define CONCAT2(a, b) CONCAT(a, b)

#define STATIC_ASSERT(condition)                                               \
  int CONCAT2(some_array, __LINE__)[(condition) ? 1 : -1]

#ifdef __GNUC__

struct s
{
  char x;

  // struct-typed member with alignment
  struct inner
  {
    int a;
  } inner __attribute__((aligned(64)));
};

STATIC_ASSERT(sizeof(struct s)==128);

#endif

int main()
{
}
