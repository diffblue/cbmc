int main()
{
  _Bool u, x, y, z;
  _Bool A, B, C, D;

  A = (u==0);
  B = (x>5);
  C = (y<6);
  D = (z==0);

  __CPROVER_input("A", A);
  __CPROVER_input("B", B);
  __CPROVER_input("C", C);
  __CPROVER_input("D", D);

  if ( (A || B) && (C || D) )
  {
  /* instructions */
  }
  else
  {
  /* instructions */
  }

  return 1;
}
