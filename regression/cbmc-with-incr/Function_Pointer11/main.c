unsigned nondet_uint();
unsigned fritz(unsigned x) { return x+1; }
unsigned franz(unsigned x) { return x; }

typedef unsigned (fun_t)(unsigned);

fun_t *f;

int main(int argc, char **argv)
{
  unsigned x = nondet_uint();
  __CPROVER_assume(x>20);
  if(x<10)
    f=0;
  else
    f=franz;

  // should be fine, and pass without warning
  f(x);
} 
