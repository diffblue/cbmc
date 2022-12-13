int main()
{
  int x;
  int y;

  do
  {
    y = 10;
    goto label;
    x = 1; // dead code, makes sure the above goto is not removed
  label:;
    _Bool nondet;
    if(nondet)
      __CPROVER_assert(y != 10, "violated via first loop");
    else
      __CPROVER_assert(y != 20, "violated via second loop");

    if(x % 2)
      break; // this statement must not cause the loop counter to be reset
  } while(1);

  y = 20;
  goto label;
}
