void *malloc(__CPROVER_size_t);

int main()
{
  int *p = malloc(sizeof(int));
  if(p != (int*)0)
  {
    int *q = malloc(sizeof(int));
    __CPROVER_assert (p != q, "same memory allocated twice");
  }
  return 0;
}
