int main()
{
  _Bool A, B, C;

  __CPROVER_input("A", A);
  __CPROVER_input("B", B);
  __CPROVER_input("C", C);

  if (A && B && C)
  {
    /* instructions */
  }

  return 1;
}
