// Test case: Verify loop hashes are stable when source locations change
// This file is designed to be modified by adding comments/whitespace before loops
// to verify that line number changes don't affect loop hashes

int main()
{
  int sum = 0;

  // Test loop 1: Basic for loop
  for(int i = 0; i < 10; i++)
  {
    sum += i;
  }

  // Test loop 2: While loop
  int j = 0;
  while(j < 5)
  {
    sum += j;
    j++;
  }

  return sum;
}
