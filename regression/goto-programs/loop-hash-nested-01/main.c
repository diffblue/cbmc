// Test program with nested loops for hash uniqueness verification
// Each loop should have a unique hash identifier

int main()
{
  int sum = 0;

  // Outer loop
  for(int i = 0; i < 3; i++)
  {
    // Inner loop 1
    for(int j = 0; j < 3; j++)
    {
      sum += i * j;
    }

    // Inner loop 2 (sibling to inner loop 1)
    for(int k = 0; k < 2; k++)
    {
      sum += i + k;
    }
  }

  return sum;
}
