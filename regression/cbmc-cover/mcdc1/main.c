int main()
{
  // Condition and decision coverage can be had with 2 tests,
  // but MC/DC needs six (n+1 for n conditions).

  __CPROVER_bool A, B, C, D, E;

  if ((A || B) && C && D && E)
  {
  }
  else
  {
  }
}
