#define CONCAT(a, b) a##b
#define CONCAT2(a, b) CONCAT(a, b)

#define STATIC_ASSERT(condition)                                               \
  int CONCAT2(some_array, __LINE__)[(condition) ? 1 : -1]

// The result of boolean operators is always an int
STATIC_ASSERT(sizeof(1.0 && 1.0)==sizeof(int));
STATIC_ASSERT(sizeof(1.0 || 1.0)==sizeof(int));
STATIC_ASSERT(sizeof(!1.0)==sizeof(int));

int main()
{
}
