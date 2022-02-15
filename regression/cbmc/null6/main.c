char *guard_malloc_counter = 0;

void *my_malloc(int size)
{
  _Bool nondet;
  guard_malloc_counter++;
  if(nondet)
    return 0;
  return (void *)guard_malloc_counter;
}

int main()
{
  int *ptr = my_malloc(sizeof(int));
  if(ptr != 0)
    __CPROVER_assert(0, "reached");
}
