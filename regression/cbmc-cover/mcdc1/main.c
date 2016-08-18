int main()
{
  // Condition and decision coverage can be had with 2 tests,
  // but MC/DC needs six (n+1 for n conditions).

  __CPROVER_bool A, B, C, D, E;

  __CPROVER_input("A", A);
  __CPROVER_input("B", B);
  __CPROVER_input("C", C);
  __CPROVER_input("D", D);
  __CPROVER_input("E", E);

  if ((A || B) && C && D && E)
  {
  }
  else
  {
  }

  return 1;
}
