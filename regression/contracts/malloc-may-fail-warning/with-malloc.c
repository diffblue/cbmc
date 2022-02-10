void *malloc(__CPROVER_size_t size)
{
  return __CPROVER_allocate(size, 0);
}

void main()
{
  int *p = malloc(sizeof(int));
  __CPROVER_assert(p != NULL, "malloc-may-fail is not set");
}
