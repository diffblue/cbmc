int main()
{
  _Bool A, B, C, D, E, F;

  __CPROVER_input("A", A);
  __CPROVER_input("B", B);
  __CPROVER_input("C", C);
  __CPROVER_input("D", D);
  __CPROVER_input("E", D);
  __CPROVER_input("F", D);

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
    if (E || F)
    {
      /* instructions */
    }
    else
    {
      /* instructions */
    }
  }

  return 1;
}
