// Test program to demonstrate hash-based loop identification
// The loop identifiers should remain stable even when we add
// unrelated code before or after the loops.

int main()
{
  int sum = 0;

  // Loop 1: Simple for loop
  for(int i = 0; i < 10; i++)
  {
    sum += i;
  }

  // Loop 2: While loop
  int j = 0;
  while(j < 5)
  {
    sum += j * 2;
    j++;
  }

  return sum;
}
