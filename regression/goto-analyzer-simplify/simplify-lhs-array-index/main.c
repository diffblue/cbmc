void main()
{
  int arr[4] = {1, 2, 3, 4};

  // No simplification
  arr[0] = 1;

  // Can simplify
  int constant = 1;
  arr[constant] = 2;

  // No simplification
  int nondet;
  arr[nondet] = 3;
}
