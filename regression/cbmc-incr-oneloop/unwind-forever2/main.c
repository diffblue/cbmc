extern int nondet_int();
int main()
{
  int x = nondet_int();
  __CPROVER_assume(0 <= x && x <= 1);
  // no error within loop => will unwind forever if no loop bound is given
  while(x < 4)
  {
    x = x + 1;
    assert(x <= 4);
  }
  assert(x < 4); // goto-symex never gets here unless it detects the loop bound
}
