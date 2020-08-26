void main()
{
  int array[] = {1, 2, 3, 4, 5};

  int *pointer = array;

  // Simplify -> array[0] = 5
  *pointer = 5;

  int nondet;
  pointer[nondet] = 6;

  // TODO: Currently writing to an offset pointer sets the domain to top
  // so recreate the variables to reign the domain back in
  int new_array[] = {1, 2, 3, 4, 5};
  int *new_pointer = new_array;

  int constant = 1;
  new_pointer[constant] = 7;
}
