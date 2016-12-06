int main()
{
  _Bool A, B, C, D;

  __CPROVER_input("A", A);
  __CPROVER_input("B", B);
  __CPROVER_input("C", C);
  __CPROVER_input("D", D);

  if (A && B)
  {
    if (C || D)
    {
      /* instructions */
    }
    else
    {
      /* instructions */
    }
  }
  else
  {
    /* instructions */
  }

  return 1;
}
