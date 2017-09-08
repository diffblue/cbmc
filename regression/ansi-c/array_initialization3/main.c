#define STATIC_ASSERT_sizeof(condition) \
  int[(condition) ? 1 : -1]

int A[];
int B[];

int A[1]={sizeof(A)};
int B[1]={sizeof(STATIC_ASSERT_sizeof(sizeof(B)==sizeof(int)))};

int main()
{
  return 0;
}
