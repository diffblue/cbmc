int main()
{
  _Bool A, B, C;

  __CPROVER_input("A", A);
  __CPROVER_input("B", B);
  __CPROVER_output("C", C);

  C = (A || B);

  if (C)
  {
    /* instructions */  
  }

  return 1;
}
