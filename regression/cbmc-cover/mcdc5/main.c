int main()
{
  __CPROVER_bool A, B, C, D;

  __CPROVER_input("A", A);
  __CPROVER_input("B", B);
  __CPROVER_input("C", C);
  __CPROVER_input("D", D);

  if((A || B)  && (C || D))
  {
  }
  else
  {
  }

  return 1;
}
