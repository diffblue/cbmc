void main()
{
  int symbol_a;
  int symbol_b;

  int nondet;
  int *nondet_pointer;
  if(nondet > 0)
  {
    nondet_pointer = &symbol_a;
  }
  else
  {
    nondet_pointer = &symbol_b;
  }

  int *arr[] = {&symbol_a, &symbol_b, nondet_pointer};

  // Simplify the pointer
  *arr[0] = 1;

  // Simplify index and the pointer
  int constant1 = 1;
  *arr[constant1] = 2;

  // Simplify the index but not the pointer
  int constant2 = 2;
  *arr[constant2] = 3;

  // No simplification
  int nondet_index;
  *arr[nondet_index] = 4;
}
