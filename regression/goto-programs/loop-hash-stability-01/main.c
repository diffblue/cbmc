// Test program with simple loops for hash stability verification
// The loop hashes should remain stable across multiple runs

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

  // Loop 3: Do-while loop
  int k = 0;
  do
  {
    sum += k;
    k++;
  } while(k < 3);

  return sum;
}
