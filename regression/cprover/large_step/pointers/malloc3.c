void *malloc(__CPROVER_size_t);
void free(void *);

int main()
{
  int *p = malloc(sizeof(int));
  int *q = malloc(sizeof(int));
  __CPROVER_assert(!__CPROVER_same_object(p, q), "property 1"); // should pass
}
