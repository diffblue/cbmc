void *malloc(__CPROVER_size_t);
void free(void *);

struct List
{
  char *data;
};

void *p;

int main()
{
  struct List *list;
  __CPROVER_assume(__CPROVER_rw_ok(list));

  p = malloc(123);
  free(p);

  __CPROVER_assert(__CPROVER_rw_ok(list), "property 1");
}
