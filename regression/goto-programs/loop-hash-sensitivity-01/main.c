// Test case: Loops with CHANGED CONDITIONS
// These loops should have DIFFERENT hashes compared to test_location_stability.c
// because the loop conditions are different

int main()
{
  int sum = 0;

  // Test loop 1: Changed upper bound from 10 to 20
  for(int i = 0; i < 20; i++)
  { // Changed: was i < 10
    sum += i;
  }

  // Test loop 2: Changed condition operator
  int j = 0;
  while(j <= 5)
  { // Changed: was j < 5
    sum += j;
    j++;
  }

  return sum;
}
