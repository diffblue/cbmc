void *malloc(__CPROVER_size_t);

struct my_allocatort
{
  void *(*allocate)(__CPROVER_size_t);
};

int main()
{
  struct my_allocatort allocator = {malloc};
  void *p = allocator.allocate(1);
  __CPROVER_assert(__CPROVER_rw_ok(p, 1), "property 1");
}
