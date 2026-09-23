void *malloc(__CPROVER_size_t);
void free(void *);

int main()
{
  int *p = malloc(sizeof(int));
  int *q = malloc(sizeof(int));
  free(p);
  __CPROVER_assert(!__CPROVER_LIVE_OBJECT(p), "property 1"); // should pass
  __CPROVER_assert(__CPROVER_LIVE_OBJECT(q), "property 2");  // should pass
}
