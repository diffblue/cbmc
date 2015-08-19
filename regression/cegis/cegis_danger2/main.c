int nondet_int();

static int __CPROVER_synthesis_writeonly_danger_invariant;
static int __CPROVER_synthesis_ignore_D_x0;
static int __CPROVER_synthesis_ignore_D_x;
static int __CPROVER_synthesis_ignore_D_x_prime;
static int __CPROVER_synthesis_ignore_G_x;
static int __CPROVER_synthesis_ignore_A_x;

// Generated from source program
static int __CPROVER_synthesis_const_x;
static int __CPROVER_synthesis_private_arg_forall_x;

void __CPROVER_synthesis_init()
{
  __CPROVER_synthesis_const_x=0;
}

void __CPROVER_synthesis_guard()
{
  __CPROVER_synthesis_ignore_G_x=__CPROVER_synthesis_const_x < 2;
}

void __CPROVER_synthesis_assertion()
{
  __CPROVER_synthesis_ignore_A_x=__CPROVER_synthesis_const_x == 10;
}

void __CPROVER_synthesis_body()
{
  ++__CPROVER_synthesis_const_x;
}
// Generated from source program

void __CPROVER_synthesis_danger_invariant();  // Danger invariant to synthesise.

void __CPROVER_synthesis_root()
{
  __CPROVER_synthesis_init();
  __CPROVER_synthesis_danger_invariant();
  __CPROVER_synthesis_ignore_D_x0=__CPROVER_synthesis_writeonly_danger_invariant;
  if (!__CPROVER_synthesis_ignore_D_x0) return;
  __CPROVER_synthesis_const_x=__CPROVER_synthesis_private_arg_forall_x;
  __CPROVER_synthesis_danger_invariant();
  __CPROVER_synthesis_ignore_D_x=__CPROVER_synthesis_writeonly_danger_invariant;
  __CPROVER_synthesis_guard();
  __CPROVER_synthesis_assertion();
  __CPROVER_synthesis_body();
  __CPROVER_synthesis_danger_invariant();
  __CPROVER_synthesis_ignore_D_x_prime=__CPROVER_synthesis_writeonly_danger_invariant;
}

int main(void)
{
  __CPROVER_synthesis_private_arg_forall_x=nondet_int();
  __CPROVER_synthesis_root();
  __CPROVER_assert(
      __CPROVER_synthesis_ignore_D_x0
          && (!(__CPROVER_synthesis_ignore_D_x && __CPROVER_synthesis_ignore_G_x)
              || __CPROVER_synthesis_ignore_D_x_prime)
          && (!(__CPROVER_synthesis_ignore_D_x
              && !__CPROVER_synthesis_ignore_G_x)
              || !__CPROVER_synthesis_ignore_A_x), "");
  return 0;
}
