typedef struct _pair
{
  int x;
  int y;
} pair;

int __VERIFIER_nondet_int();

int main(void)
{
  pair p1 = {.x = 0, .y = __VERIFIER_nondet_int()};
  pair p2 = {};
  p2.x = __VERIFIER_nondet_int();

  __CPROVER_assert(p1.x == p2.y, "true by constant propagation");

  return 0;
}
