#define CONCAT(a, b) a##b
#define CONCAT2(a, b) CONCAT(a, b)

#define STATIC_ASSERT(condition)                                               \
  int CONCAT2(some_array, __LINE__)[(condition) ? 1 : -1]

int A[];
int B[];

int A[1]={sizeof(A)};
int B[1]={sizeof(STATIC_ASSERT_sizeof(sizeof(B)==sizeof(int)))};

int main()
{
  return 0;
}
