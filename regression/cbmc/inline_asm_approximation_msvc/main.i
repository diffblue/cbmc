// MSVC-style __asm blocks have no operand interface: a block containing an
// instruction that is not modeled may change any variable it names (with
// shadowing, any local variable of that name) and any memory it can reach.
int global;

int main(void)
{
  int z = 0;
  __asm { nop }
  __CPROVER_assert(z == 0, "nop is modeled"); // holds

  int x = 0, y = 0;
  {
    int x = 0;
    __asm { mov x, 1 }
    __CPROVER_assert(x == 0, "inner x"); // fails
  }
  __CPROVER_assert(x == 0, "outer x");            // fails
  __CPROVER_assert(y == 0, "y is not named");     // holds
  __CPROVER_assert(global == 0, "static object"); // fails

  return 0;
}
