int *object;
_Bool create_object;
void allocator(void) {
  __CPROVER_assume(create_object);
  object = __CPROVER_allocate(sizeof(int), 1);
  create_object = 0;
}
int main() {
  __CPROVER_ASYNC_1: allocator();
  create_object = 1;
  __CPROVER_assume(create_object == 0);
  *object = 42;
}
