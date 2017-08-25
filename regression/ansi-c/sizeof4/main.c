
#define STATIC_ASSERT(condition) \
  int some_array##__LINE__[(condition) ? 1 : -1];

// The result of boolean operators is always an int
STATIC_ASSERT(sizeof(1.0 && 1.0)==sizeof(int));
STATIC_ASSERT(sizeof(1.0 || 1.0)==sizeof(int));
STATIC_ASSERT(sizeof(!1.0)==sizeof(int));

int main()
{
}
