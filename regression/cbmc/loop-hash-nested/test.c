// Test program with nested loops
// Each loop should have a unique hash identifier

int main()
{
  int sum = 0;

  // Outer loop
  for(int i = 0; i < 3; i++)
  {
    // Inner loop
    for(int j = 0; j < 3; j++)
    {
      sum += i * j;
    }
  }

  return sum;
}
