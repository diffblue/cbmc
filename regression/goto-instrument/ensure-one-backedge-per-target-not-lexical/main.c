_Bool nondet_bool();

int main()
{
  int j = 0;
  int i;
L2:
  ++j;
  if(j == 2)
    return 0;
  int extra_counter = 0;
  for(int i = nondet_bool() ? -1 : -2; extra_counter < 10; ++i, ++extra_counter)
  {
    // The following causes a surprising loop unwinding failure (and an equally
    // surprising sequence of loop unwinding status output) when using
    // --unwind 4 --unwinding-assertions
    // No such failure can be observed when using "goto L2X" instead and
    // enabling the below label/goto pair.
    if(i >= 1)
      goto L2;
  }
  //L2X:
  //   goto L2;
  return 0;
}
