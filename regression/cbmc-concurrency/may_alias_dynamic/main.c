// Test shared pointer to malloc'd object (the original issue #790 example).
int *object;
_Bool create_object;

void allocator(void)
{
  __CPROVER_assume(create_object);
  object = __CPROVER_allocate(sizeof(int), 1);
  *object = 42;
  create_object = 0;
}

int main()
{
  __CPROVER_ASYNC_1: allocator();
  create_object = 1;
  __CPROVER_assume(create_object == 0);
  __CPROVER_assert(*object == 42, "object value");
}
