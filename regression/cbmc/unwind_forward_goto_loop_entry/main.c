// The inner loop is entered by an unconditional forward goto. Its unwinding
// counter must restart on each entry: it runs 3 times per outer iteration,
// so --unwind 3 suffices.
int main(void)
{
  int i = 0;
outer:;
  int j = 0;
  goto inner;
  return 1;
inner:
  j++;
  if(j < 3)
    goto inner;
  i++;
  if(i < 2)
    goto outer;
  return 0;
}
