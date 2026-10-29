int posix_memalign(void **, __CPROVER_size_t, __CPROVER_size_t);

int main()
{
  void *ptr;
  posix_memalign(&ptr, sizeof(void *), sizeof(int));
  __CPROVER_assert(__CPROVER_r_ok(ptr, sizeof(int)), "property 1");
  return 0;
}
