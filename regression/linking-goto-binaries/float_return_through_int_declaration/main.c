// h is declared without a prototype and the return type int (C17 6.5.2.2/9:
// calling a function through an incompatible type is undefined); supp.c
// defines it returning double.  Linking the goto binaries converts the
// result to the declared int, as a call of a function returning int would
// receive it.
int h();

int main()
{
  int r = h(2.5);
  __CPROVER_assert(r == 2, "the result converted to int");
  __CPROVER_assert(r == 3, "WRONG (must FAIL)");
  return 0;
}
