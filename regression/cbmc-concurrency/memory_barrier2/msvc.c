volatile int turn;
int x;
volatile int flag1 = 0, flag2 = 0;

void *thr1(void *arg)
{
  flag1 = 1;
  turn = 1;
  __asm { mfence; }
  __CPROVER_assume(!(flag2 == 1 && turn == 1));
  x = 0;
  __CPROVER_assert(x <= 0, "");
  flag1 = 0;
}

void *thr2(void *arg)
{
  flag2 = 1;
  turn = 0;
  __asm { mfence; }
  __CPROVER_assume(!(flag1 == 1 && turn == 0));
  x = 1;
  __CPROVER_assert(x >= 1, "");
  flag2 = 0;
}

int main()
{
__CPROVER_ASYNC_1:
  thr1(0);
  thr2(0);
}
