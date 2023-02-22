union U
{
  void *ptr;
  __CPROVER_size_t n;
};

int main()
{
  int *p = __CPROVER_allocate(sizeof(int), 0);
  union U u = {.ptr = p};
  __CPROVER_assert(u.n != 0, "is not null");
}
