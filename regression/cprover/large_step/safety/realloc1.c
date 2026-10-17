void *malloc(__CPROVER_size_t);
void *realloc(void *, __CPROVER_size_t);
void free(void *);

int main()
{
  int *p = malloc(sizeof(int));
  int *q = realloc(p, sizeof(int) * 2);
  __CPROVER_assert(__CPROVER_LIVE_OBJECT(q), "property 1"); // passes
  __CPROVER_assert(
    __CPROVER_OBJECT_SIZE(q) == sizeof(int) * 2, "property 2"); // passes
  free(p);
}
