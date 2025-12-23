// Test case: Same loops as test_location_stability.c but shifted by adding comments
// The loop hashes should remain IDENTICAL despite line number changes

// Adding multiple comment lines to shift all code down
// Comment line 2
// Comment line 3
// Comment line 4
// Comment line 5
// Comment line 6
// Comment line 7
// Comment line 8
// Comment line 9
// Comment line 10

int main()
{
  int sum = 0;

  // Adding more comments before the loop to shift its location
  // Comment A
  // Comment B
  // Comment C

  // Test loop 1: Basic for loop (now at a different line number)
  for(int i = 0; i < 10; i++)
  {
    sum += i;
  }

  // More comments between loops
  // Comment D
  // Comment E

  // Test loop 2: While loop (now at a different line number)
  int j = 0;
  while(j < 5)
  {
    sum += j;
    j++;
  }

  return sum;
}
