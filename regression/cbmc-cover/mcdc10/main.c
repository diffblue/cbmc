int main()
{
  _Bool A, B, C;

  __CPROVER_input("cold", A);
  __CPROVER_input("raining", B);
  __CPROVER_input("windy", C);

  if ( A || B || C )
  {
  /* instructions */
  }
  else
  {
  /* instructions */
  }

  return 1;
}
