// Test program with different loop types
// Each loop should have a unique hash identifier

int main()
{
  int sum = 0;

  // For loop
  for(int i = 0; i < 5; i++)
  {
    sum += i;
  }

  // While loop
  int j = 0;
  while(j < 5)
  {
    sum += j;
    j++;
  }

  // Do-while loop
  int k = 0;
  do
  {
    sum += k;
    k++;
  } while(k < 5);

  return sum;
}
