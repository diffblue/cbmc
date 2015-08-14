int nondet_int();

// Sketch pattern (allows to synthesise multiple functions - orthogonal to grammar!)
static int __CPROVER_synthesis_writeonly_result;
static int __CPROVER_synthesis_arg_x;
static int __CPROVER_synthesis_arg_y;

int __CPROVER_synthesis_learn();  // To synthesise

void __CPROVER_synthesis_root()
{
  __CPROVER_synthesis_learn();
  if (__CPROVER_synthesis_writeonly_result) __CPROVER_synthesis_writeonly_result=__CPROVER_synthesis_arg_x;
  else __CPROVER_synthesis_writeonly_result=__CPROVER_synthesis_arg_y;
}
// Sketch pattern

int main(void)
{
  __CPROVER_synthesis_arg_x=nondet_int();
  __CPROVER_synthesis_arg_y=nondet_int();
  __CPROVER_synthesis_root();
  __CPROVER_assert(
      __CPROVER_synthesis_writeonly_result >= __CPROVER_synthesis_arg_x && __CPROVER_synthesis_writeonly_result >= __CPROVER_synthesis_arg_y
          && (__CPROVER_synthesis_writeonly_result == __CPROVER_synthesis_arg_x
              || __CPROVER_synthesis_writeonly_result == __CPROVER_synthesis_arg_y), "");
  return 0;
}
