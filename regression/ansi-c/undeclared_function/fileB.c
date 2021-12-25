void *malloc(__CPROVER_size_t s)
{
  return (void *)0 + s;
}

int f()
{
  malloc(4);
}
