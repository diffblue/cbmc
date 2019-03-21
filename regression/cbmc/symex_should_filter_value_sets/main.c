#include <assert.h>

static void noop()
{
}

int main(int argc, char **argv)
{
  __CPROVER_assume(argc == 5);

  int a = 2;
  int b = 1;
  int *ptr_to_a_or_b = argv[0][0] == '0' ? &a : &b;

  // Should work (value-set filtered by assume):
  int *p1 = ptr_to_a_or_b;
  __CPROVER_assume(p1 != &a);
  int c1 = *p1;

  int *p2 = ptr_to_a_or_b;
  __CPROVER_assume(*p2 != 2);
  int c2 = *p2;

  // Should work (value-set filtered by else):
  int c3 = 0;
  int *p3 = ptr_to_a_or_b;
  if(p3 == &a)
  {
  }
  else
  {
    c3 = *p3;
  }

  int c4 = 0;
  int *p4 = ptr_to_a_or_b;
  if(*p4 == 2)
  {
  }
  else
  {
    c4 = *p4;
  }

  // Should work (value-set filtered by if):
  int c5 = 0;
  int *p5 = ptr_to_a_or_b;
  if(p5 != &a)
  {
    c5 = *p5;
  }

  int c6 = 0;
  int *p6 = ptr_to_a_or_b;
  if(*p6 != 2)
  {
    c6 = *p6;
  }

  // Should work (value-set filtered by assume before a backward goto):
  int *p7 = ptr_to_a_or_b;
  goto check7;

divide7:
  int c7 = *p7;
  goto end_test7;

check7:
  __CPROVER_assume(p7 != &a);
  goto divide7;

end_test7:

  int *p8 = ptr_to_a_or_b;
  goto check8;

divide8:
  int c8 = *p8;
  goto end_test8;

check8:
  __CPROVER_assume(*p8 != 2);
  goto divide8;

end_test8:

  // Should work (value-set filtered by confluence of if and else):
  int *p9 = ptr_to_a_or_b;
  if(argv[1][0] == '0')
    __CPROVER_assume(p9 != &a);
  else
    __CPROVER_assume(p9 != &a);
  int c9 = *p9;

  int *p10 = ptr_to_a_or_b;
  if(argv[2][0] == '0')
    __CPROVER_assume(*p10 != 2);
  else
    __CPROVER_assume(*p10 != 2);
  int c10 = *p10;

  // Should work (value-set filtered by assume, write through an unrelated
  // pointer has no effect):
  int c = 0;
  int *ptr_to_c = &c;

  int *p11 = ptr_to_a_or_b;
  __CPROVER_assume(p11 != &a);
  *ptr_to_c = 3;
  int c11 = *p11;

  int *p12 = ptr_to_a_or_b;
  __CPROVER_assume(*p12 != 2);
  *ptr_to_c = 4;
  int c12 = *p12;

  // Should work (value-set filtered by assume, function call has no effect):
  int *p13 = ptr_to_a_or_b;
  __CPROVER_assume(p13 != &a);
  noop();
  int c13 = *p13;

  int *p14 = ptr_to_a_or_b;
  __CPROVER_assume(*p14 != 2);
  noop();
  int c14 = *p14;

  // Shouldn't work (unsafe as value-set only filtered by if on one branch):
  int *p15 = ptr_to_a_or_b;
  if(argv[3][0] == '0')
    __CPROVER_assume(p15 != &a);
  else
  {
  }
  int c15 = *p15;

  int *p16 = ptr_to_a_or_b;
  if(argv[4][0] == '0')
    __CPROVER_assume(*p16 != 2);
  else
  {
  }
  int c16 = *p16;

  assert(0);
}
