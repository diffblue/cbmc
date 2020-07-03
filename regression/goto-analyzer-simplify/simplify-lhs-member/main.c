struct test_struct
{
  int *pointer_component;
  int array[5];
};

void main()
{
  int symbol;

  struct test_struct value;

  // Simplify a pointer inside a struct
  int symbol;
  value.pointer_component = &symbol;

  // Simplify
  *value.pointer_component = 5;

  int nondet;
  if(nondet > 0)
  {
    value.pointer_component = &nondet;
  }
  else
  {
    value.pointer_component = &symbol;
  }

  // No simplification
  *value.pointer_component = 6;

  // Simplify an array

  // Can simplify
  int constant = 1;
  value.array[constant] = 2;

  // No simplification
  int nondet;
  value.array[nondet] = 3;
}
