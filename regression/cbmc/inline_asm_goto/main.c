// asm goto: a statement that is not modeled may jump to any of its labels, or
// fall through; a modeled statement (none of the modeled instructions jumps)
// falls through.
static int branch(int *p)
{
  // not modeled: may jump to either label or fall through
  asm goto("testl %0, %0; jz %l[zero]; jmp %l[nonzero]"
           :
           : "r"(*p)
           :
           : zero, nonzero);
  return 0;
zero:
  return 1;
nonzero:
  return 2;
}

static int modeled(void)
{
  // modeled, and does not jump
  asm goto("nop" : : : : out);
  return 0;
out:
  return 1;
}

int main(void)
{
  int x = 0;
  int r = branch(&x);
  __CPROVER_assert(r != 0, "falls through");                           // fails
  __CPROVER_assert(r != 1, "jumps to zero");                           // fails
  __CPROVER_assert(r != 2, "jumps to nonzero");                        // fails
  __CPROVER_assert(r >= 0 && r <= 2, "one of the labels");             // holds
  __CPROVER_assert(modeled() == 0, "modeled statement does not jump"); // holds
  return 0;
}
