void *thr1(void *arg)
{
  for(int i = 0; i < *(int *)arg; ++i)
    ;

  return 0;
}

int l1 = 1;
int l2 = 2;

int main()
{
__CPROVER_ASYNC_1:
  thr1(&l1);
__CPROVER_ASYNC_2:
  thr1(&l2);
}
