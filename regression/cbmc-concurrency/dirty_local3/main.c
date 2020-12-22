void worker(int *p)
{
  __CPROVER_assert(*p == 1, "reading from dirty object");
}

void create_thread(int **p)
{
#ifdef locals_bug
  int z = 1;
__CPROVER_ASYNC_1:
  worker(&z);
#else
__CPROVER_ASYNC_1:
  worker(*p);
#endif
}

int main()
{
  int y = 1;
  int *x[1] = {&y};
  create_thread(&x[0]);
  return 0;
}
