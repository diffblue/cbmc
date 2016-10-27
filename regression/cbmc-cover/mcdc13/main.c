int main()
{
  _Bool A, B;

  __CPROVER_input("A", A);
  __CPROVER_input("B", B);

  if (A && B)
  {
    /* instructions */
  }

  return 1;
}
