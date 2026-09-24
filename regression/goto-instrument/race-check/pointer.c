int x;

void thread(int *p)
{
  *p = 1;
}

int main(void)
{
__CPROVER_ASYNC_0:
  thread(&x);
  x = 2;
  return 0;
}
