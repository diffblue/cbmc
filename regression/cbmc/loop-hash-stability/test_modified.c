// Modified test program with pseudo-loops added before the real loops
// The real loops should maintain their hash identifiers

int main()
{
  int sum = 0;

  // Add some pseudo-loops (do-while-0 pattern) that should not affect
  // the hash values of the real loops below
  do
  {
    sum += 1;
  } while(0);
  do
  {
    sum += 2;
  } while(0);
  do
  {
    sum += 3;
  } while(0);

  // Loop 1: Simple for loop (same as before)
  for(int i = 0; i < 10; i++)
  {
    sum += i;
  }

  // Loop 2: While loop (same as before)
  int j = 0;
  while(j < 5)
  {
    sum += j * 2;
    j++;
  }

  return sum;
}
