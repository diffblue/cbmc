// Regression test: a label defined before a nested function definition must
// stay visible to a goto that appears after the nested function. Previously
// the nested function's type-checking cleared the enclosing function's label
// bookkeeping, so this was rejected with "branching label 'start' is not
// defined in function".
int main(void)
{
  int x = 0;

  int inc(int y)
  {
    return y + 1;
  }

start:
  x = inc(x);
  if(x < 5)
    goto start;

  __CPROVER_assert(x == 5, "goto loop straddling a nested function reaches 5");

  return 0;
}
