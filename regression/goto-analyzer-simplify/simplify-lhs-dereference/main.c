void main()
{
  int symbol;

  int *pointer = &symbol;

  // Simplify
  *pointer = 5;

  int nondet;
  if(nondet > 0)
  {
    pointer = &nondet;
  }
  else
  {
    pointer = &symbol;
  }

  // No simplification
  *pointer = 6;
}
