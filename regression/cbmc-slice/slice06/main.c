#define N 10

int main()
{
  int i;
  int sum = 0;
  int product = 1;
  for(i = 1; i < N; ++i) {
    sum = sum + i;
    product = product * i;
  }
  assert(sum>0);

  return 0;
}
