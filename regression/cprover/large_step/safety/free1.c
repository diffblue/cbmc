void *malloc(__CPROVER_size_t);
void free(void *);

int main()
{
  int *p = malloc(sizeof(int));
  __CPROVER_assert(__CPROVER_LIVE_OBJECT(p), "property 1"); // passes
  free(p);
  __CPROVER_assert(__CPROVER_LIVE_OBJECT(p), "property 2"); // fails
}
