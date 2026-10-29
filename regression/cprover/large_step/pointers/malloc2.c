void *malloc(__CPROVER_size_t);

int *p;

#define N (sizeof(int) * 10)

int main()
{
  p = malloc(N);
  __CPROVER_assert(__CPROVER_OBJECT_SIZE(p) == N, "property 1");
  return 0;
}
