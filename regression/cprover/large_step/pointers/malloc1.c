void *malloc(__CPROVER_size_t);

int *p;

int main()
{
  p = malloc(sizeof(int) * 10);
  p[2] = 123;
  __CPROVER_assert(p[2] == 123, "property 1");
  return 0;
}
